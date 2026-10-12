/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap92.Lemma_92_27_1_Category

/-!
# Affine-space realization of `C_{X/Λ}`

Objects of `AlgebraicGeometry.AlgebraicSpace.Cotangent.category Λ X` are morphisms
`U ⟶ A` in `Over (Spec Λ)` with `U` étale over `X` and `A` a polynomial affine space.
This leaf records the scheme-valued realization `(U ⟶ A) ↦ A` and the underlying map
`U ⟶ A`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Cotangent

variable (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ))

/-- The scheme-valued realization sending an object `(U ⟶ A)` of `C_{X/Λ}` to the polynomial
affine space `A`. -/
def affineScheme : category Λ X ⥤ Scheme.{u} where
  obj x := x.right.obj.left
  map f := f.right.hom.left
  map_id := fun _ ↦ sorry
  map_comp := fun _ _ ↦ sorry

/-- The realization of `(U ⟶ A)` is the underlying scheme of the polynomial affine space. -/
theorem affineScheme_obj (x : category Λ X) :
    (affineScheme Λ X).obj x = x.right.obj.left :=
  sorry

/-- A morphism of `C_{X/Λ}` acts on affine spaces by the underlying scheme map of the
`Over (Spec Λ)` component. -/
theorem affineScheme_map {x y : category Λ X} (f : x ⟶ y) :
    (affineScheme Λ X).map f = f.right.hom.left :=
  sorry

/-- The underlying scheme morphism `U ⟶ A` of an object of `C_{X/Λ}`. -/
def homToAffine (x : category Λ X) :
    ((smallEtaleToOver X).obj x.left).left ⟶ x.right.obj.left :=
  x.hom.left

/-- The morphism `homToAffine Λ X x` is the left component of the `Over (Spec Λ)` morphism `x.hom`. -/
theorem homToAffine_eq_hom_left (x : category Λ X) :
    homToAffine Λ X x = x.hom.left :=
  sorry

/-- The morphism `U ⟶ A` of an object of `C_{X/Λ}` lies over `Spec Λ`. -/
theorem homToAffine_over (x : category Λ X) :
    homToAffine Λ X x ≫ x.right.obj.hom = ((smallEtaleToOver X).obj x.left).hom :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Cotangent
