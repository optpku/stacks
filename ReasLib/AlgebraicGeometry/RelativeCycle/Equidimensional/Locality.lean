module

public import ReasLib.AlgebraicGeometry.RelativeCycle.Equidimensional
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Reduced
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CyclesOnFibers.SupportOperations

/-!
# Zariski locality of equidimensional relative cycles

Equidimensionality is characterized by the relative dimension of the reduced
closure of the support and may be checked on open covers of the source and target.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Hom.CyclesOnFibers
open Scheme.Hom
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RelativeCycle

/-- The reduced induced structure on the closure of the support of a family of
`r`-cycles on fibres. -/
noncomputable abbrev reducedSupportClosure {X S : Scheme.{u}} {f : X ⟶ S} [LocallyOfFiniteType f]
    {r : ℕ} (α : f.FiberCycleFamily r) :
    Scheme.ClosedSubschemeStructure (TopologicalSpace.Closeds.closure (support α)) :=
  Scheme.ClosedSubschemeStructure.reduced
    (TopologicalSpace.Closeds.closure (support α))

/-- Equidimensionality of a family of `r`-cycles on fibres is equivalent to the
reduced induced closed subscheme on the closure of its support having relative
dimension at most `r` over `S`. -/
theorem equidimensional_iff_closure {X S : Scheme.{u}} {f : X ⟶ S} [LocallyOfFiniteType f] {r : ℕ}
    (α : f.FiberCycleFamily r) :
    Equidimensional α ↔
      RelativeDimensionLE ((reducedSupportClosure α).ι ≫ f) r := sorry

/-- Equidimensionality of a relative `r`-cycle may be checked after restriction
to the members of an open cover of the source. -/
theorem equidimensional_iff_of_source_iSup_eq_top
    {X S : Scheme.{u}} [IsLocallyNoetherian S] {f : X ⟶ S} [LocallyOfFiniteType f]
    {r : ℕ} (α : f.FiberCycleFamily r) (hα : IsRelative α) {ι : Type u}
    (U : ι → X.Opens) (hU : iSup U = ⊤) :
    Equidimensional α ↔
      ∀ i, Equidimensional (FiberCycleFamily.restrict (U i) ⊤ le_top α) := sorry

/-- Equidimensionality of a relative `r`-cycle may be checked after restriction
to the preimages of the members of an open cover of the target. -/
theorem equidimensional_iff_of_target_iSup_eq_top
    {X S : Scheme.{u}} [IsLocallyNoetherian S] {f : X ⟶ S} [LocallyOfFiniteType f]
    {r : ℕ} (α : f.FiberCycleFamily r) (hα : IsRelative α) {κ : Type u}
    (V : κ → S.Opens) (hV : iSup V = ⊤) :
    Equidimensional α ↔
      ∀ j, Equidimensional (FiberCycleFamily.restrict (f ⁻¹ᵁ V j) (V j) le_rfl α) := sorry

/-- Equidimensionality of a relative `r`-cycle over a locally Noetherian base
with locally finite-type structure morphism may be checked on open covers of
the source and target. -/
theorem isEquidimensional_iff_of_iSup_eq_top
    {X S : Scheme.{u}} [IsLocallyNoetherian S] {f : X ⟶ S} [LocallyOfFiniteType f]
    {r : ℕ} (α : f.FiberCycleFamily r) (hα : IsRelative α) {ι κ : Type u}
    (U : ι → X.Opens) (hU : iSup U = ⊤) (V : κ → S.Opens) (hV : iSup V = ⊤) :
    Equidimensional α ↔
      ∀ i j, Equidimensional
        (FiberCycleFamily.restrict (U i ⊓ f ⁻¹ᵁ V j) (V j) inf_le_right α) := sorry

end AlgebraicGeometry.RelativeCycle
