/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Gluing.DoubleAlong.PuncturedAffineSpace
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.Factorization

/-!
# Factorization obstructions for doubled punctured affine space

This module records the failure of quasi-compactness for the canonical charts of
infinite-dimensional affine space doubled along its punctured open and the resulting
obstruction to certain factorizations.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.PuncturedAffineSpace.DoubleAlong

/-- A canonical chart of an infinite-dimensional affine space doubled along its punctured
open is not quasi-compact. -/
theorem chartMap_not_quasiCompact
    (ι : Type u) [Infinite ι] (k : Type u) [CommRing k] [Nontrivial k]
    (j : Fin 2) : ¬ QuasiCompact (chartMap ι k j) := sorry

/-- Neither canonical chart of countably generated affine space with doubled origin factors
as a closed immersion followed by a morphism of finite presentation. -/
theorem countableChartMap_not_closedImmersion_finitePresentation_factorization
    (k : Type u) [Field k] (j : Fin 2) :
    ¬ (MorphismProperty.comp @IsClosedImmersion
      (@Scheme.Hom.FinitePresentation : MorphismProperty Scheme))
      (chartMap (ULift.{u} ℕ) k j) := by
  intro h
  exact chartMap_not_quasiCompact (ULift.{u} ℕ) k j
    (Scheme.Hom.FinitePresentation.closedImmersion_comp_le_quasiCompact
      (chartMap (ULift.{u} ℕ) k j) h)

end AlgebraicGeometry.PuncturedAffineSpace.DoubleAlong
