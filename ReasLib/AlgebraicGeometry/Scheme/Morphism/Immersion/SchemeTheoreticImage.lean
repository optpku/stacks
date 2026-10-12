/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Closure
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Immersion.Reduced

/-!
# Scheme-theoretic images of immersions

The canonical map from an immersion to its scheme-theoretic image is an open immersion with
dense range when the morphism is quasi-compact or its source is reduced.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The canonical map from an immersion to its scheme-theoretic image is an open immersion if
the morphism is quasi-compact or its source is reduced. -/
theorem isOpenImmersion_toImage_of_quasiCompact_or_isReduced
    {X Z : Scheme.{u}} (h : Z ⟶ X) [IsImmersion h]
    (hqc_or_red : QuasiCompact h ∨ IsReduced Z) :
    IsOpenImmersion h.toImage := sorry

/-- The open range of the canonical map from an immersion to its scheme-theoretic image is
scheme-theoretically dense if the morphism is quasi-compact or its source is reduced. -/
theorem schemeTheoreticallyDense_opensRange_toImage_of_quasiCompact_or_isReduced
    {X Z : Scheme.{u}} (h : Z ⟶ X) [IsImmersion h]
    (hqc_or_red : QuasiCompact h ∨ IsReduced Z) :
    schemeTheoreticallyDense (@opensRange _ _ h.toImage
      (isOpenImmersion_toImage_of_quasiCompact_or_isReduced h hqc_or_red)) := sorry

/-- The canonical map from an immersion to its scheme-theoretic image is dominant if the
morphism is quasi-compact or its source is reduced. -/
theorem isDominant_toImage_of_quasiCompact_or_isReduced
    {X Z : Scheme.{u}} (h : Z ⟶ X) [IsImmersion h]
    (hqc_or_red : QuasiCompact h ∨ IsReduced Z) :
    IsDominant h.toImage := sorry

end AlgebraicGeometry.Scheme.Hom
