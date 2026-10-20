module

public import ReasLib.Algebra.Category.CommRingCat.PolynomialResolution.Functoriality
public import ReasLib.AlgebraicTopology.SimplicialObject.Homotopy
public import Mathlib.CategoryTheory.CommSq

/-!
# Diagonal homotopies of standard polynomial resolutions

A diagonal factorization of a commutative square identifies the induced map of standard
polynomial resolutions, up to simplicial homotopy, with the composite through the diagonal
and the identity-algebra standard resolution.
-/

@[expose] public section

open CategoryTheory
open Opposite
open Under
open CommRingCat.Under
open PolynomialResolution

universe u

noncomputable section

namespace CategoryTheory.CommRingCat.Under
namespace PolynomialResolution

/-- Commutativity of a ring-map square, rewritten on the structure morphisms of the
corresponding under-objects. -/
theorem under_mk_comm {A B A' B' : CommRingCat.{u}}
    (α : A ⟶ B) (ρ : A ⟶ A') (β : A' ⟶ B') (φ : B ⟶ B')
    (h_comm : ρ ≫ β = α ≫ φ) :
    ρ ≫ (Under.mk β).hom = (Under.mk α).hom ≫ φ :=
  sorry

/-- The map of standard resolutions, as simplicial rings, induced by a commutative square of
ring maps. -/
def functorialitySimplicial {A A' : CommRingCat.{u}} {B : Under A} {B' : Under A'}
    (ρ : A ⟶ A') (φ : B.right ⟶ B'.right)
    (h_comm : ρ ≫ B'.hom = B.hom ≫ φ) :
    standardSimplicial A B ⟶ standardSimplicial A' B' where
  app n := ((functorialityMap ρ φ h_comm).app n).right
  naturality _ _ _ := sorry

/-- Components of `functorialitySimplicial` are the underlying ring maps of `functorialityMap`. -/
theorem functorialitySimplicial_app {A A' : CommRingCat.{u}} {B : Under A} {B' : Under A'}
    (ρ : A ⟶ A') (φ : B.right ⟶ B'.right)
    (h_comm : ρ ≫ B'.hom = B.hom ≫ φ) (n : SimplexCategoryᵒᵖ) :
    (functorialitySimplicial ρ φ h_comm).app n =
      ((functorialityMap ρ φ h_comm).app n).right :=
  sorry

/-- The map of standard resolutions associated to a commutative square of ring maps. -/
def functorialitySimplicial_mk {A B A' B' : CommRingCat.{u}}
    (α : A ⟶ B) (ρ : A ⟶ A') (β : A' ⟶ B') (φ : B ⟶ B')
    (h_comm : ρ ≫ β = α ≫ φ) :
    standardSimplicial A (Under.mk α) ⟶ standardSimplicial A' (Under.mk β) :=
  @functorialitySimplicial A A' (Under.mk α) (Under.mk β) ρ φ (under_mk_comm α ρ β φ h_comm)

/-- Unfolding of `functorialitySimplicial_mk` through the under-object functoriality map. -/
theorem functorialitySimplicial_mk_eq {A B A' B' : CommRingCat.{u}}
    (α : A ⟶ B) (ρ : A ⟶ A') (β : A' ⟶ B') (φ : B ⟶ B')
    (h_comm : ρ ≫ β = α ≫ φ) :
    functorialitySimplicial_mk α ρ β φ h_comm =
      @functorialitySimplicial A A' (Under.mk α) (Under.mk β) ρ φ
        (under_mk_comm α ρ β φ h_comm) :=
  sorry

/-- The structure morphism of the identity-algebra standard resolution, as a map of simplicial
rings from the constant object. -/
def structureSection (A : CommRingCat.{u}) :
    (SimplicialObject.const CommRingCat.{u}).obj A ⟶
      standardSimplicial A (Under.mk (𝟙 A)) where
  app n := (((evaluation A).obj (Under.mk (𝟙 A))).left.obj n).hom
  naturality _ _ _ := sorry

/-- Components of `structureSection` are the structure maps of the identity-algebra standard
terms. -/
theorem structureSection_app (A : CommRingCat.{u}) (n : SimplexCategoryᵒᵖ) :
    (structureSection A).app n =
      (((evaluation A).obj (Under.mk (𝟙 A))).left.obj n).hom :=
  sorry

/-- The forgotten augmentation of the standard resolution, as a map of simplicial rings. -/
def forgottenAugmentation (A : CommRingCat.{u}) (B : Under A) :
    standardSimplicial A B ⟶ (SimplicialObject.const CommRingCat.{u}).obj B.right where
  app n := (((evaluation A).obj B).hom.app n).right
  naturality _ _ _ := sorry

/-- Components of `forgottenAugmentation` are the underlying ring maps of the standard
augmentations. -/
theorem forgottenAugmentation_app (A : CommRingCat.{u}) (B : Under A)
    (n : SimplexCategoryᵒᵖ) :
    (forgottenAugmentation A B).app n =
      (((evaluation A).obj B).hom.app n).right :=
  sorry

/-- The composite `P_• ⟶ B ⟶ A' ⟶ P'_•` of forgotten augmentation, the constant map on the
diagonal, the identity-algebra structure section, and identity-algebra functoriality. -/
def throughDiagonal {A B A' B' : CommRingCat.{u}}
    (α : A ⟶ B) (β : A' ⟶ B') (κ : B ⟶ A') :
    standardSimplicial A (Under.mk α) ⟶ standardSimplicial A' (Under.mk β) :=
  forgottenAugmentation A (Under.mk α) ≫
    (SimplicialObject.const CommRingCat.{u}).map κ ≫
    structureSection A' ≫
    functorialitySimplicial_mk (𝟙 A') (𝟙 A') β β (Eq.refl (𝟙 A' ≫ β))

/-- Unfolding of `throughDiagonal` as the four-fold composite through the identity-algebra
standard resolution. -/
theorem throughDiagonal_eq {A B A' B' : CommRingCat.{u}}
    (α : A ⟶ B) (β : A' ⟶ B') (κ : B ⟶ A') :
    throughDiagonal α β κ =
      forgottenAugmentation A (Under.mk α) ≫
        (SimplicialObject.const CommRingCat.{u}).map κ ≫
        structureSection A' ≫
        functorialitySimplicial_mk (𝟙 A') (𝟙 A') β β (Eq.refl (𝟙 A' ≫ β)) :=
  sorry

/-- A commutative square of ring maps with a diagonal making both triangles commute induces
a map of standard resolutions homotopic to the composite through the diagonal and the
identity-algebra standard resolution. -/
theorem functorialitySimplicial_homotopic_throughDiagonal
    {A B A' B' : CommRingCat.{u}} {α : A ⟶ B} {ρ : A ⟶ A'} {β : A' ⟶ B'} {φ : B ⟶ B'}
    (sq : CommSq ρ α β φ) (κ : B ⟶ A')
    (h_left : α ≫ κ = ρ) (h_right : κ ≫ β = φ) :
    SimplicialObject.Homotopic
      (functorialitySimplicial_mk α ρ β φ sq.w)
      (throughDiagonal α β κ) :=
  sorry

end PolynomialResolution
end CategoryTheory.CommRingCat.Under

