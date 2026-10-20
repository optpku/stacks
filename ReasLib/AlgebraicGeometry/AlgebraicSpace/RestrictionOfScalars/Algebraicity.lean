/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RestrictionOfScalars
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.HomSmall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FiniteLocallyFree.Basic
public import Mathlib.Logic.Small.Basic

/-!
# Algebraicity of restriction of scalars

Restriction-of-scalars pairs admit a model in the base universe. When the
morphism to the base is finite locally free, this model is an algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RestrictionOfScalars

namespace Pair

/-- Restriction-of-scalars pairs over a test scheme form a small type. -/
theorem small {S : Scheme.{u}} {X Z B : AlgebraicSpace S} (f : X ⟶ Z)
    (g : Z ⟶ B) (T : Over S) : Small.{u} (Pair f g T) :=
  small_map sigmaEquiv

/-- A model in the base universe for the type of restriction-of-scalars pairs. -/
def smallType {S : Scheme.{u}} {X Z B : AlgebraicSpace S} (f : X ⟶ Z)
    (g : Z ⟶ B) (T : Over S) : Type u :=
  @Shrink.{u} (Pair f g T) (small f g T)

/-- Restriction-of-scalars pairs are equivalent to their small model. -/
def smallEquiv {S : Scheme.{u}} {X Z B : AlgebraicSpace S} (f : X ⟶ Z)
    (g : Z ⟶ B) (T : Over S) : Pair f g T ≃ smallType f g T :=
  @equivShrink.{u} (Pair f g T) (small f g T)

end Pair

/-- The small presheaf of restriction-of-scalars pairs, with maps induced by precomposition. -/
def smallFunctor {S : Scheme.{u}} {X Z B : AlgebraicSpace S} (f : X ⟶ Z)
    (g : Z ⟶ B) : (Over S)ᵒᵖ ⥤ Type u where
  obj T := Pair.smallType f g T.unop
  map {T T'} h := TypeCat.ofHom fun p ↦
    Pair.smallEquiv f g T'.unop
      (Pair.precomp h.unop ((Pair.smallEquiv f g T.unop).symm p))
  map_id := by
    intro T
    ext p
    exact (congrArg (Pair.smallEquiv f g T.unop)
      (Pair.precomp_id _)).trans ((Pair.smallEquiv f g T.unop).apply_symm_apply p)
  map_comp := by
    intro T₁ T₂ T₃ φ ψ
    ext p
    dsimp
    rw [Equiv.symm_apply_apply, Pair.precomp_comp]

/-- Evaluating the small restriction-of-scalars presheaf gives the small model of pairs. -/
theorem smallFunctor_obj {S : Scheme.{u}} {X Z B : AlgebraicSpace S} (f : X ⟶ Z)
    (g : Z ⟶ B) (T : Over S) :
    (smallFunctor f g).obj (op T) = Pair.smallType f g T := rfl

/-- Sections of the small restriction-of-scalars presheaf are restriction-of-scalars pairs. -/
def smallFunctor_equiv {S : Scheme.{u}} {X Z B : AlgebraicSpace S} (f : X ⟶ Z)
    (g : Z ⟶ B) (T : Over S) : (smallFunctor f g).obj (op T) ≃ Pair f g T :=
  (Pair.smallEquiv f g T).symm

/-- Universe lifting identifies the small model with the restriction-of-scalars presheaf. -/
def smallFunctorUliftIso {S : Scheme.{u}} {X Z B : AlgebraicSpace S} (f : X ⟶ Z)
    (g : Z ⟶ B) : smallFunctor f g ⋙ uliftFunctor.{u + 1, u} ≅
      restrictionOfScalars f g :=
  NatIso.ofComponents
    (fun T ↦ Equiv.toIso
      (Equiv.ulift.trans (smallFunctor_equiv f g T.unop)))
    (by
      intro T T' h
      ext p
      exact (Pair.smallEquiv f g T'.unop).symm_apply_apply _)

/-- Restriction of scalars along a finite locally free morphism is an algebraic space. -/
instance instIsAlgebraicSpace {S : Scheme.{u}} {X Z B : AlgebraicSpace S}
    (f : X ⟶ Z) (g : Z ⟶ B) [FiniteLocallyFree g] :
    IsAlgebraicSpace (smallFunctor f g) :=
  sorry

/-- The algebraic space of restriction of scalars along a finite locally free morphism. -/
def space {S : Scheme.{u}} {X Z B : AlgebraicSpace S} (f : X ⟶ Z) (g : Z ⟶ B)
    [FiniteLocallyFree g] : AlgebraicSpace S :=
  ofIsAlgebraicSpace (smallFunctor f g)

/-- The functor of points of the restriction-of-scalars space is its small presheaf. -/
theorem space_functorOfPoints {S : Scheme.{u}} {X Z B : AlgebraicSpace S}
    (f : X ⟶ Z) (g : Z ⟶ B) [FiniteLocallyFree g] :
    (space f g).functorOfPoints = smallFunctor f g := rfl

/-- The universe-raised sheaf of points of the restriction-of-scalars space is the sheaf of pairs. -/
def spaceSheafIso {S : Scheme.{u}} {X Z B : AlgebraicSpace S} (f : X ⟶ Z)
    (g : Z ⟶ B) [FiniteLocallyFree g] :
    toSheaf.obj (space f g) ≅ sheaf f g :=
  (fullyFaithfulSheafToPresheaf (Scheme.fppfTopology.over S) (Type (u + 1))).preimageIso
    (smallFunctorUliftIso f g)

end AlgebraicGeometry.AlgebraicSpace.RestrictionOfScalars
