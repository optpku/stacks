/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeHom.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FiniteLocallyFree
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.HomSmall
public import Mathlib.CategoryTheory.Comma.LocallySmall
public import Mathlib.Logic.Small.Basic

/-!
# Algebraicity of relative morphisms

Relative morphisms admit a small model of their presheaf. When the source is
finite locally free over the base, this model is an algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeHom

namespace Pair

/-- Relative-morphism pairs over a test scheme form a small type. -/
theorem small {S : Scheme.{u}} {B Z X : AlgebraicSpace S}
    (z : Z ⟶ B) (x : X ⟶ B) (T : Over S) : Small.{u} (Pair z x T) := by
  apply small_of_injective
    (f := fun p : Pair z x T ↦
      (⟨p.a, p.b⟩ : Σ a : ofOver T ⟶ B, BaseChangeMorphism z x a))
  intro p q h
  cases p
  cases q
  cases h
  rfl

/-- A model in the base universe for the type of relative-morphism pairs. -/
def smallType {S : Scheme.{u}} {B Z X : AlgebraicSpace S}
    (z : Z ⟶ B) (x : X ⟶ B) (T : Over S) : Type u :=
  @Shrink.{u} (Pair z x T) (small z x T)

/-- Relative-morphism pairs are equivalent to their small model. -/
def smallEquiv {S : Scheme.{u}} {B Z X : AlgebraicSpace S}
    (z : Z ⟶ B) (x : X ⟶ B) (T : Over S) : Pair z x T ≃ smallType z x T :=
  @equivShrink.{u} (Pair z x T) (small z x T)

end Pair

/-- The small presheaf of morphisms from `Z` to `X` relative to their base. -/
def smallFunctor {S : Scheme.{u}} {B : AlgebraicSpace S} (Z X : Over B) :
    (Over S)ᵒᵖ ⥤ Type u where
  obj T := Pair.smallType Z.hom X.hom T.unop
  map {T T'} h := TypeCat.ofHom fun p ↦
    Pair.smallEquiv Z.hom X.hom T'.unop
      (((Pair.smallEquiv Z.hom X.hom T.unop).symm p).restrict h.unop)
  map_id := by
    intro T
    ext p
    exact (congrArg (Pair.smallEquiv Z.hom X.hom T.unop)
      (Pair.restrict_id _)).trans ((Pair.smallEquiv Z.hom X.hom T.unop).apply_symm_apply p)
  map_comp := by
    intro T₁ T₂ T₃ φ ψ
    ext p
    dsimp
    rw [Equiv.symm_apply_apply, Pair.restrict_comp]

/-- Evaluation of the small relative-morphism presheaf is the small model of pairs. -/
theorem smallFunctor_obj {S : Scheme.{u}} {B : AlgebraicSpace S} (Z X : Over B)
    (T : Over S) :
    (smallFunctor Z X).obj (op T) = Pair.smallType Z.hom X.hom T := rfl

/-- Sections of the small relative-morphism presheaf are relative-morphism pairs. -/
def smallFunctor_equiv {S : Scheme.{u}} {B : AlgebraicSpace S} (Z X : Over B)
    (T : Over S) : (smallFunctor Z X).obj (op T) ≃ Pair Z.hom X.hom T :=
  (Pair.smallEquiv Z.hom X.hom T).symm

/-- Universe lifting identifies the small model with the canonical relative-morphism presheaf. -/
def smallFunctorUliftIso {S : Scheme.{u}} {B : AlgebraicSpace S} (Z X : Over B) :
    smallFunctor Z X ⋙ uliftFunctor.{u + 1, u} ≅ presheaf Z.hom X.hom :=
  NatIso.ofComponents
    (fun T ↦ Equiv.toIso
      (Equiv.ulift.trans (smallFunctor_equiv Z X T.unop)))
    (by
      intro T T' h
      ext p
      exact (Pair.smallEquiv Z.hom X.hom T'.unop).symm_apply_apply _)

/-- Relative morphisms from a finite locally free algebraic space form an algebraic space. -/
instance instIsAlgebraicSpace {S : Scheme.{u}} {B : AlgebraicSpace S}
    {Z X : Over B} [FiniteLocallyFree Z.hom] :
    IsAlgebraicSpace (smallFunctor Z X) :=
  sorry

/-- The algebraic space of relative morphisms from a finite locally free source. -/
def space {S : Scheme.{u}} {B : AlgebraicSpace S} (Z X : Over B)
    [FiniteLocallyFree Z.hom] : AlgebraicSpace S :=
  ofIsAlgebraicSpace (smallFunctor Z X)

/-- The functor of points of the relative-morphism space is its small presheaf. -/
theorem space_functorOfPoints {S : Scheme.{u}} {B : AlgebraicSpace S}
    (Z X : Over B) [FiniteLocallyFree Z.hom] :
    (space Z X).functorOfPoints = smallFunctor Z X := rfl

/-- The sheaf of points of the relative-morphism space is the canonical relative-morphism sheaf. -/
def spaceSheafIso {S : Scheme.{u}} {B : AlgebraicSpace S} (Z X : Over B)
    [FiniteLocallyFree Z.hom] : toSheaf.obj (space Z X) ≅ sheaf Z.hom X.hom :=
  (fullyFaithfulSheafToPresheaf (Scheme.fppfTopology.over S) (Type (u + 1))).preimageIso
    (smallFunctorUliftIso Z X)

end AlgebraicGeometry.AlgebraicSpace.RelativeHom
