import Lake

open System Lake DSL

package emcm where
  srcDir := "src"
  version := v!"0.1.0"
  description :=
  "Compute (co)homology and suspension maps of Eilenberg-MacLane spaces using Cartan-Moore constructions."

require "leanprover" / Cli @ git "v4.29.0"

lean_lib EMCM
lean_lib EMCMCli

@[default_target]
lean_exe emcm where
  root := `EMCMCli.Main
  extraDepTargets := #[`writeVersion]

target writeVersion : FilePath := do
  let pkg ← Lake.getRootPackage
  let outfile := pkg.srcDir / "EMCMCli" / "Version.lean"
  IO.FS.writeFile outfile s!"-- Auto-generated
namespace EMCMCli
def version : String := \"{pkg.version}\""
  return .pure outfile (caption := "Write version source file")
