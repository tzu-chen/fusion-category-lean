/-
  FusionCategory/tools/AuditList.lean

  Gate 4, batch item B2 (a): MECHANICAL generation of the audit list.

  This file proves nothing.  Elaborating it inspects the *elaborated
  environment* of the whole package and prints, to stdout, one tab-separated
  record per constant declared by a module of the package:

      <name> <TAB> <kind> <TAB> <declaring module> <TAB> <projection? 0/1>

  "Declared by a module of the package" is decided by `Environment.getModuleIdxFor?`
  and `Environment.header.moduleNames`, i.e. by the module the constant was
  actually added from -- not by a name prefix, so declarations that live
  outside the `FusionCategory` namespace but inside the package's files
  (`FusionRing`, `FPData` in `Basic.lean`) are included, and nothing from
  Mathlib is.

  Excluded: unsafe/partial declarations (their axiom dependence is not
  well defined) and internal names (`Name.isInternal`: private declarations and
  compiler-generated auxiliaries, all of which Lean forbids a user from
  naming).  Excluding them hides nothing: `#print axioms` recurses through the
  values of every constant it meets, so an audited parent already covers its
  auxiliaries.

  Scope.  The single import is the library root `FusionCategory`, so the
  environment holds exactly the package's *built surface*: the 22 modules in
  the import closure of `FusionCategory.lean`.  Source files outside that
  closure are reported, and probed, by `tools/gen-audit.sh` (see its
  "pariah" step) so that a module which declares something and is not
  imported by the root cannot slip out of the audit unnoticed.

  Usage:  lean tools/AuditList.lean            (with the package's oleans on LEAN_PATH)
          lake env lean tools/AuditList.lean

  Driver: tools/gen-audit.sh.

  This file is static: the driver prepends nothing and the import block is
  fixed, so the tool that produces the audit list is reviewable in one screen.
-/
import FusionCategory

open Lean

namespace AuditList

/-- The package namespace root. -/
def pkgRoot : Name := `FusionCategory

/-- A module belongs to the package when it is `FusionCategory` or a submodule of it. -/
def isPackageModule (n : Name) : Bool := pkgRoot.isPrefixOf n

/-- The `ConstantInfo` constructor, as a short stable string. -/
def kindOf : ConstantInfo → String
  | .axiomInfo _  => "axiom"
  | .defnInfo _   => "def"
  | .thmInfo _    => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _   => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _   => "constructor"
  | .recInfo _    => "recursor"

end AuditList

open AuditList in
run_cmd do
  let env ← Lean.getEnv
  let mods := env.header.moduleNames
  let rows : Array (Name × String × Name) :=
    env.constants.fold
      (fun acc n ci =>
        if ci.isUnsafe || n.isInternal then acc
        else
          match env.getModuleIdxFor? n with
          | none => acc
          | some idx =>
            let m := mods[idx.toNat]!
            if isPackageModule m then acc.push (n, kindOf ci, m) else acc)
      #[]
  -- Deterministic order: by name, byte-wise on the rendered string.
  let rows := rows.qsort (fun a b => a.1.toString < b.1.toString)
  for (n, k, m) in rows do
    -- `isProjectionFn` is Lean's own answer to "is this a structure projection?",
    -- not a guess from the name: a Prop-valued structure field is declared as a
    -- theorem, so `kind` alone cannot tell the two apart.
    let proj := if env.isProjectionFn n then "1" else "0"
    IO.println s!"{n}\t{k}\t{m}\t{proj}"
