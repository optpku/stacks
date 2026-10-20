module

public import ReasLib.AlgebraicGeometry.Scheme.RelativeHom.Morphism

/-!
# Relative morphisms of schemes

This module defines the relative-Hom presheaf in a slice category of schemes.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.RelativeHom

/-- The relative-Hom presheaf associated to `Z` and `X` over `S`, sending an
`S`-scheme `T` to the type of morphisms `T ⊗ Z ⟶ X` over `S`. -/
def functor {S : Scheme.{u}} (Z X : Over S) : (Over S)ᵒᵖ ⥤ Type u :=
  ((tensoringRight (Over S)).obj Z).op ⋙ yoneda.obj X

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Base-change morphisms over a test scheme are equivalent to morphisms from
its product with `Z` to `X` over the base scheme. -/
noncomputable def baseChangeMorphismEquiv {S : Scheme.{u}} (Z X T : Over S) :
    BaseChangeMorphism Z X T ≃ (functor Z X).obj (.op T) where
  toFun b := by
    change T ⊗ Z ⟶ X
    exact Over.homMk
      (eqToHom (Over.tensorObj_left T Z) ≫ b.left ≫ pullback.snd T.hom X.hom) (by
        calc
          (eqToHom (Over.tensorObj_left T Z) ≫ b.left ≫ pullback.snd T.hom X.hom) ≫
              X.hom =
            eqToHom (Over.tensorObj_left T Z) ≫
              (b.left ≫ (Over.mk (pullback.fst T.hom X.hom) : Over T.left).hom) ≫
                T.hom := by
                  rw [Category.assoc, Category.assoc, ← pullback.condition]
                  rfl
          _ = eqToHom (Over.tensorObj_left T Z) ≫
              (Over.mk (pullback.fst T.hom Z.hom) : Over T.left).hom ≫ T.hom := by
                rw [b.w]
          _ = (T ⊗ Z).hom := by rfl)
  invFun g := by
    change T ⊗ Z ⟶ X at g
    exact Over.homMk
      (pullback.lift (pullback.fst T.hom Z.hom)
        (eqToHom (Over.tensorObj_left T Z).symm ≫ g.left) (by
          rw [Category.assoc, g.w]
          rfl)) (by simp)
  left_inv b := by
    ext
    dsimp
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
      exact b.w.symm
    · simp
  right_inv g := by
    change T ⊗ Z ⟶ X at g
    apply Over.OverMorphism.ext
    dsimp
    simp

/-- The value of the relative-Hom presheaf at `T` is the type of morphisms
`T ⊗ Z ⟶ X` over the base scheme. -/
theorem functor_obj {S : Scheme.{u}} (Z X T : Over S) :
    (functor Z X).obj (.op T) = (T ⊗ Z ⟶ X) := sorry

/-- Pullback in the relative-Hom presheaf is precomposition by tensoring the
test-scheme morphism with `Z`. -/
theorem functor_map {S : Scheme.{u}} (Z X : Over S) {T' T : Over S}
    (f : T' ⟶ T) (g : T ⊗ Z ⟶ X) :
    (functor Z X).map f.op g = (f ▷ Z) ≫ g := sorry

end AlgebraicGeometry.Scheme.RelativeHom
