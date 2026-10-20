/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Sections.Limit
public import ReasLib.CategoryTheory.DerivedCategory.Limit.Compatibility
import Mathlib.Tactic.CrossRefAttribute

/-!
# Stalkwise stage comparisons for derived limits

The canonical map to a stage is built from an explicit homotopy-limit presentation.  A companion
accepts the legacy `IsDerivedLimit` witness through its canonical presentation, so callers never
need to expose a product object, an inclusion into it, or a local product instance.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived.Limit

variable {X : RingedSpace.{u}}

/-- The degree-`m` additive cohomology tower of derived sections over an open. -/
@[stacks 0D61 "open cohomology tower of a sequential derived system"]
abbrev cohomologyTower (X : RingedSpace.{u}) (U : Opens X.carrier)
    (Ksys : SequentialInverseSystem (ModuleDerived X)) (m : ℤ) :
    SequentialInverseSystem AddCommGrpCat.{u} :=
  (Ksys ⋙ moduleDerivedSectionsAtOpenToAb X U) ⋙
    DerivedCategory.homologyFunctor AddCommGrpCat.{u} m

/-- The local Milnor vanishing and eventual injectivity conditions at a point and a fixed target
stage. -/
@[stacks 0D61 "local Milnor conditions for a stalkwise stage comparison"]
def LocalMilnorConditions (X : RingedSpace.{u})
    (Ksys : SequentialInverseSystem (ModuleDerived X))
    (x : X) (m : ℤ) (n₀ : ℕ) : Prop :=
  ∀ W : Opens X.carrier, x ∈ W →
    ∃ U : Opens X.carrier,
      x ∈ U ∧ U ≤ W ∧ IsZero ((cohomologyTower X U Ksys (m - 1)).firstDerivedLimit) ∧
        ∀ n : ℕ, ∀ hn : n₀ ≤ n, Mono ((cohomologyTower X U Ksys m).transitionMap hn)

/-- The map on degree-`m` cohomology sheaves induced by the projection from a presented
homotopy limit to stage `n`. -/
@[stacks 0D61 "cohomology-sheaf map to a stage of a derived limit"]
noncomputable def cohomologyStageMap
    {Ksys : SequentialInverseSystem (ModuleDerived X)} {K : ModuleDerived X}
    (P : HomotopyLimit.Presentation Ksys K) (m : ℤ) (n : ℕ) :
    (DerivedCategory.homologyFunctor X.Modules m).obj K ⟶
      (DerivedCategory.homologyFunctor X.Modules m).obj (Ksys.obj (op n)) :=
  (DerivedCategory.homologyFunctor X.Modules m).map (P.stageProjection n)

/-- Local Milnor conditions make the cohomology stage map monic after taking the stalk at the
chosen point. -/
@[stacks 0D61 "stalkwise monomorphism of a cohomology stage map"]
theorem cohomologyStageMap_stalkMono
    {Ksys : SequentialInverseSystem (ModuleDerived X)} {K : ModuleDerived X}
    (P : HomotopyLimit.Presentation Ksys K) (x : X) (m : ℤ) (n₀ : ℕ)
    (hlocal : LocalMilnorConditions X Ksys x m n₀) :
    Mono (RingedSpace.moduleStalkHom x (cohomologyStageMap P m n₀)) := sorry

/-- Legacy `IsDerivedLimit` form of stalkwise monicity of the canonical stage projection. -/
@[stacks 0D61 "stalkwise monomorphism of a derived-limit stage projection"]
theorem stageProjection_stalkMono
    {Ksys : SequentialInverseSystem (ModuleDerived X)} {K : ModuleDerived X}
    (hK : IsDerivedLimit Ksys K) (x : X) (m : ℤ) (n₀ : ℕ)
    (hlocal : LocalMilnorConditions X Ksys x m n₀) :
    Mono (RingedSpace.moduleStalkHom x
      ((DerivedCategory.homologyFunctor X.Modules m).map (hK.stageProjection n₀))) := sorry

/-- Function-level injectivity companion to `stageProjection_stalkMono`. -/
@[stacks 0D61 "injectivity of a derived-limit stage projection on a cohomology stalk"]
theorem stageProjection_stalkInjective
    {Ksys : SequentialInverseSystem (ModuleDerived X)} {K : ModuleDerived X}
    (hK : IsDerivedLimit Ksys K) (x : X) (m : ℤ) (n₀ : ℕ)
    (hlocal : LocalMilnorConditions X Ksys x m n₀) :
    Function.Injective (RingedSpace.moduleStalkMap x
      ((DerivedCategory.homologyFunctor X.Modules m).map (hK.stageProjection n₀))) := sorry

end AlgebraicGeometry.RingedSpace.ModuleDerived.Limit

end
