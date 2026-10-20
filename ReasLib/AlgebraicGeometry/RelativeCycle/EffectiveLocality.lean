module

public import ReasLib.AlgebraicGeometry.RelativeCycle.Effective
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberCycleFamily.Operations

/-!
# Zariski locality of effectiveness of relative cycles

Effectiveness of a relative cycle can be checked on open covers of the source,
the target, or both simultaneously.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RelativeCycle

/-- Effectiveness of a relative `r`-cycle may be checked after restriction to
the members of an open cover of the source. -/
theorem isEffective_iff_of_source_iSup_eq_top
    {X S : Scheme.{u}} [IsLocallyNoetherian S] {f : X ⟶ S} [LocallyOfFiniteType f]
    {r : ℕ} (α : f.FiberCycleFamily r) (hα : IsRelative α) {ι : Type u}
    (U : ι → X.Opens) (hU : iSup U = ⊤) :
    IsEffective α ↔
      ∀ i, IsEffective
        (AlgebraicGeometry.Scheme.Hom.FiberCycleFamily.restrict (U i) ⊤ le_top α) := sorry

/-- Effectiveness of a relative `r`-cycle may be checked after restriction to
the preimages of the members of an open cover of the target. -/
theorem isEffective_iff_of_target_iSup_eq_top
    {X S : Scheme.{u}} [IsLocallyNoetherian S] {f : X ⟶ S} [LocallyOfFiniteType f]
    {r : ℕ} (α : f.FiberCycleFamily r) (hα : IsRelative α) {κ : Type u}
    (V : κ → S.Opens) (hV : iSup V = ⊤) :
    IsEffective α ↔
      ∀ j, IsEffective
        (AlgebraicGeometry.Scheme.Hom.FiberCycleFamily.restrict (f ⁻¹ᵁ V j) (V j) le_rfl α) := sorry

/-- Effectiveness of a relative `r`-cycle may be checked on the intersections
of a source open cover with the preimages of a target open cover. -/
theorem isEffective_iff_of_iSup_eq_top
    {X S : Scheme.{u}} [IsLocallyNoetherian S] {f : X ⟶ S} [LocallyOfFiniteType f]
    {r : ℕ} (α : f.FiberCycleFamily r) (hα : IsRelative α) {ι κ : Type u}
    (U : ι → X.Opens) (hU : iSup U = ⊤) (V : κ → S.Opens) (hV : iSup V = ⊤) :
    IsEffective α ↔
      ∀ i j, IsEffective
        (AlgebraicGeometry.Scheme.Hom.FiberCycleFamily.restrict
          (U i ⊓ f ⁻¹ᵁ V j) (V j) inf_le_right α) := sorry

end AlgebraicGeometry.RelativeCycle
