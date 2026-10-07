module

import Lean

public import ReasLib.AlgebraicGeometry.Scheme.Module.Cech.Ordered.Functoriality
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cech.PrincipalOpen

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace ModuleCech

variable {X : Scheme.{u}}

/-- The bounded principal-open Čech complex, functorial in its module argument. -/
noncomputable def ofSectionsFunctor {c : ℕ} (f : Fin c → Γ(X, ⊤)) :
    X.Modules ⥤ CochainComplex X.Modules ℕ :=
  AlgebraicGeometry.Scheme.ModuleCech.Ordered.extendedFunctor
    (fun i : ULift.{u} (Fin c) ↦ X.basicOpen (f i.down))

/-- Evaluating the principal-open Čech functor recovers `ofSections`. -/
theorem ofSectionsFunctor_obj {c : ℕ} (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules) :
    (ofSectionsFunctor f).obj ℱ = ofSections f ℱ := sorry

/-- The natural projection from the principal-open Čech complex to its degree-zero module. -/
noncomputable def ofSectionsProjection {c : ℕ} (f : Fin c → Γ(X, ⊤)) :
    ofSectionsFunctor f ⟶ CochainComplex.single₀ X.Modules :=
  AlgebraicGeometry.Scheme.ModuleCech.Ordered.projection
    (fun i : ULift.{u} (Fin c) ↦ X.basicOpen (f i.down))

end ModuleCech

end


namespace M2FDataSorryAudit

open Lean Meta Elab Command

private def containsNonPropSorry (value : Expr) : MetaM Bool := do
  let found ← IO.mkRef false
  forEachExpr value fun expr => do
    unless ← found.get do
      let (head, args) := expr.getAppFnArgs
      if head == ``sorryAx && args.size >= 1 then
        unless ← isProp args[0]! do
          found.set true
  found.get

run_cmd do
  let env ← getEnv
  -- `env.constants` also contains imported declarations.  Current-module
  -- declarations are the ones without a `const2ModIdx` entry; restricting the
  -- scan to them is important for remote compilation because `mkModuleData`
  -- materializes and traverses the entire imported environment.  That made a
  -- tiny audit scratch file hit Leanfra's cancellation deadline on large repos.
  for (name, info) in env.constants do
    if (Environment.getModuleIdxFor? env name).isNone then
      if let some value := info.value? true then
        let (hasNonPropSorry, _) ← liftCoreM <| (containsNonPropSorry value).run
        if hasNonPropSorry then
          logInfo m!"M2F_NON_PROP_DATA_SORRY|{privateToUserName name}"

end M2FDataSorryAudit
