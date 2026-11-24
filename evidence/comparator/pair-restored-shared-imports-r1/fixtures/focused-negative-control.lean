import Lean.Environment
import Lake.Check.Compare

open Lean

def loadTarget (filename : String) (target : Name) : IO LeanExport.ExportedEnv := do
  let (moduleData, _) ← readModuleData ⟨filename⟩
  let some decl := moduleData.constants.find? (·.name == target)
    | throw (IO.userError s!"Missing {target} in {filename}")
  let constants : Std.HashMap Name ConstantInfo := {}
  return { constMap := constants.insert target decl, constOrder := #[target] }

def main (args : List String) : IO Unit := do
  let [challengePath, solutionPath] := args
    | throw (IO.userError "Expected Challenge and Solution olean paths")
  let target := `ZetaComparator.pairStrict
  let challenge ← loadTarget challengePath target
  let solution ← loadTarget solutionPath target
  let expected := s!"Challenge and solution theorem statement do not match: '{target}'"
  match Lake.Check.compareAt challenge solution #[target] #[] #[] with
  | .error message =>
      if message == expected then
        IO.println message
      else
        throw (IO.userError s!"Unexpected comparison error: {message}")
  | .ok _ =>
      throw (IO.userError "Comparator accepted the changed bound")
