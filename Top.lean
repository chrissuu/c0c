/-
Top

Note: consider moving the in-house cmd line parser to a dedicated
Lean4 command line parser library.

Author: Chris Su <chrjs@cmu.edu>
-/
import C0VC

inductive EmitTarget where
  | exe
  | llvm
deriving Repr, BEq

structure CliConfig where
  infile        : Option String := none
  typecheckOnly : Bool := false
  emit          : EmitTarget := .llvm
  optLevel      : Nat := 0
  libs          : List String := []
  unsafeMode    : Bool := false
  dumpTokens    : Bool := false
  dumpAst       : Bool := false
  dumpElab      : Bool := false
  dumpTree      : Bool := false
  dumpIrRaw     : Bool := false

private def usage : String :=
  String.intercalate "\n"
    [ "usage: bin/c0vc [-Olevel] [--emit=option] [-l header.h0] [--unsafe] infile.lN"
    , "       bin/c0vc -t infile.lN"
    , "       [--dump-tokens] [--dump-ast] [--dump-elab] [--dump-tree] [--dump-ir-raw]"
    ]

private def parseNatOrZero (s : String) : Nat :=
  match s.toNat? with
  | some n => n
  | none => 0

private def parseEmit (s : String) : EmitTarget :=
  match s with
  | "exe" => .exe
  | "llvm" => .llvm
  | _ => .llvm

private def parseArgs : List String → CliConfig → Except String CliConfig
  | [], cfg => .ok cfg
  | "-t" :: rest, cfg => parseArgs rest { cfg with typecheckOnly := true }
  | "--typecheck-only" :: rest, cfg => parseArgs rest { cfg with typecheckOnly := true }
  | "--unsafe" :: rest, cfg => parseArgs rest { cfg with unsafeMode := true }
  | "--dump-tokens" :: rest, cfg => parseArgs rest { cfg with dumpTokens := true }
  | "--dump-ast" :: rest, cfg => parseArgs rest { cfg with dumpAst := true }
  | "--dump-elab" :: rest, cfg => parseArgs rest { cfg with dumpElab := true }
  | "--dump-tree" :: rest, cfg => parseArgs rest { cfg with dumpTree := true }
  | "--dump-ir-raw" :: rest, cfg => parseArgs rest { cfg with dumpIrRaw := true }
  | "-l" :: lib :: rest, cfg => parseArgs rest { cfg with libs := cfg.libs.concat lib }
  | "--lib" :: lib :: rest, cfg => parseArgs rest { cfg with libs := cfg.libs.concat lib }
  | arg :: rest, cfg =>
      if arg.startsWith "--emit=" then
        let emit := parseEmit ((arg.drop 7).toString)
        parseArgs rest { cfg with emit := emit }
      else if arg.startsWith "-e" then
        let emit := parseEmit ((arg.drop 2).toString)
        parseArgs rest { cfg with emit := emit }
      else if arg.startsWith "--opt=" then
        let optLevel := parseNatOrZero ((arg.drop 6).toString)
        parseArgs rest { cfg with optLevel := optLevel }
      else if arg.startsWith "-O" then
        let optLevel := parseNatOrZero ((arg.drop 2).toString)
        parseArgs rest { cfg with optLevel := optLevel }
      else if arg.startsWith "-l" then
        let lib := (arg.drop 2).toString
        parseArgs rest { cfg with libs := cfg.libs.concat lib }
      else if arg.startsWith "--lib=" then
        let lib := (arg.drop 6).toString
        parseArgs rest { cfg with libs := cfg.libs.concat lib }
      else if arg.startsWith "-" then
        parseArgs rest cfg
      else
        match cfg.infile with
        | none => parseArgs rest { cfg with infile := some arg }
        | some _ => .error s!"multiple input files provided: {arg}"

private def runFrontend (cfg : CliConfig) (infile : String) : IO (Except String (Option C0VC.LLVM.IR.Program)) := do
  let source ← IO.FS.readFile infile
  match C0VC.Lexer.munch infile source with
  | .error err => pure (.error err)
  | .ok tokens =>
      if cfg.dumpTokens then
        IO.println (C0VC.Token.Print.ppTokens tokens)
      let parsed := C0VC.Parse.parseProgramFromTokens tokens
      match parsed with
      | .error err => pure (.error err)
      | .ok program =>
          if cfg.dumpAst then
            IO.println (C0VC.Ast.Print.ppProgram program)
          let elabbed := C0VC.Elab.elabProgram program
          match elabbed with
          | .error err => pure (.error err)
          | .ok elabbedProgram =>
              if cfg.dumpElab then
                IO.println (C0VC.Ast.Print.ppProgram elabbedProgram)
              match C0VC.Typechecker.tc elabbedProgram with
              | .error err => pure (.error err)
              | .ok _ =>
                  if cfg.typecheckOnly then
                    pure (.ok none)
                  else
                    let dceProgram := C0VC.Dce.run elabbedProgram
                    let treeProgram := C0VC.LLVM.Tree.Trans.translate dceProgram
                    if cfg.dumpTree then
                      IO.println (C0VC.LLVM.Tree.Print.ppProgram treeProgram)
                    let llvmIR := C0VC.LLVM.Codegen.translate treeProgram
                    if cfg.dumpIrRaw then
                      IO.println (C0VC.LLVM.IR.Print.ppProgramRaw llvmIR)
                    pure (.ok (some llvmIR))

def main (args : List String) : IO UInt32 := do
  let cfgE := parseArgs args {}
  let cfg ← match cfgE with
    | .error err =>
        IO.eprintln s!"{err}\n{usage}"
        return 1
    | .ok cfg => pure cfg

  let infile ← match cfg.infile with
    | none =>
        IO.eprintln usage
        return 1
    | some file => pure file

  let frontendResult ← runFrontend cfg infile
  match frontendResult with
  | .error err =>
      IO.eprintln err
      return 1
  | .ok none =>
      return 0
  | .ok (some llvmIR) =>
        match cfg.emit with
        | .llvm =>
            C0VC.LLVM.EmitLlvm.emit llvmIR (infile ++ ".ll")
        | .exe =>
            let exe := infile ++ ".exe"
            IO.FS.writeFile exe "#!/bin/sh\necho 0\n"
            let _ ← IO.Process.output { cmd := "chmod", args := #["+x", exe] }
        return 0
