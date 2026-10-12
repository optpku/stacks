/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Scheme-theoretic image factorizations

This leaf gives the universal-property interface for a factorization through a
scheme-theoretic image. Mathlib owns the canonical construction
`Scheme.Hom.image`; the predicate below permits applications to work with an
arbitrary presentation of that image.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- A factorization of `g` through its scheme-theoretic image in `Y`. -/
def IsSchemeTheoreticImageFactorization {X Y Z : Scheme.{u}}
    (g : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y) : Prop :=
  toImage ≫ ι = g ∧ IsClosedImmersion ι ∧
    ∀ ⦃Z' : Scheme.{u}⦄ (toZ' : X ⟶ Z') (closed : Z' ⟶ Y) [IsClosedImmersion closed],
      toZ' ≫ closed = g →
      ∃! lift : Z ⟶ Z', lift ≫ closed = ι ∧ toImage ≫ lift = toZ'

namespace Scheme.Hom

/-- Mathlib's canonical `f.image` with `f.toImage` and `f.imageι` is a scheme-theoretic image
factorization. -/
@[stacks 01R6]
theorem isSchemeTheoreticImageFactorization_image {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsSchemeTheoreticImageFactorization f f.toImage f.imageι := by
  refine ⟨f.toImage_imageι, inferInstance, ?_⟩
  intro Z' toZ' closed hclosed hfac
  have hker : closed.ker ≤ f.imageι.ker := by
    rw [f.ker.ker_subschemeι, ← hfac]
    exact Scheme.Hom.le_ker_comp toZ' closed
  refine ⟨IsClosedImmersion.lift closed f.imageι hker, ?_, ?_⟩
  · refine ⟨IsClosedImmersion.lift_fac closed f.imageι hker, ?_⟩
    rw [← cancel_mono closed, Category.assoc, IsClosedImmersion.lift_fac,
      f.toImage_imageι, hfac]
  · intro lift hlift
    rw [← cancel_mono closed, hlift.1, IsClosedImmersion.lift_fac]

end Scheme.Hom

end AlgebraicGeometry
