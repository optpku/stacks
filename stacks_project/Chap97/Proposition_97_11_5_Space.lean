module

public import Mathlib.Logic.Small.Defs
public import stacks_project.Chap65.Lemma_65_16_4_IsAlgebraicSpace
public import stacks_project.Chap67.Definition_67_46_2_FiniteLocallyFree
public import stacks_project.Chap78.Definition_78_19_1_QuotientSheaf
public import stacks_project.Chap97.Lemma_97_11_1_Sheaf

/-!
# Algebraic space of restriction of scalars

If `Z ⟶ B` is finite locally free, the restriction-of-scalars functor
`Res_{Z/B}(X)` is represented by an algebraic space over `S`, obtained from the
`u`-small encoding of `Pair`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RestrictionOfScalars

namespace Pair

/-- The type of restriction-of-scalars pairs over a scheme `T` is `u`-small. -/
instance instSmall {S : Scheme.{u}} {X Z B : AlgebraicSpace S} {f : X ⟶ Z}
    {g : Z ⟶ B} (T : Over S) : Small.{u} (Pair f g T) :=
  sorry

end Pair

/-- The `u`-small functor of points of `Res_{Z/B}(X)`, sending `T` to a shrink of
the type of pairs `(a, b)`. -/
def smallFunctor {S : Scheme.{u}} {X Z B : AlgebraicSpace S} (f : X ⟶ Z)
    (g : Z ⟶ B) : (Over S)ᵒᵖ ⥤ Type u where
  obj T := Shrink (Pair f g T.unop)
  map {T T'} h :=
    TypeCat.ofHom fun p ↦
      equivShrink (Pair f g T'.unop)
        (Pair.precomp h.unop ((equivShrink (Pair f g T.unop)).symm p))
  map_id := sorry
  map_comp := sorry

/-- Evaluating `smallFunctor f g` at `T` recovers the shrink of `Pair f g T`. -/
theorem smallFunctor_obj {S : Scheme.{u}} {X Z B : AlgebraicSpace S} (f : X ⟶ Z)
    (g : Z ⟶ B) (T : Over S) :
    (smallFunctor f g).obj (op T) = Shrink (Pair f g T) :=
  sorry

/-- Values of `smallFunctor f g` are equivalent to restriction-of-scalars pairs
over `T`. -/
def smallFunctor_equiv {S : Scheme.{u}} {X Z B : AlgebraicSpace S} (f : X ⟶ Z)
    (g : Z ⟶ B) (T : Over S) : (smallFunctor f g).obj (op T) ≃ Pair f g T :=
  (equivShrink (Pair f g T)).symm

/-- Universe lifting of `smallFunctor f g` recovers the restriction-of-scalars
functor `Res_{Z/B}(X)`. -/
def smallFunctorUliftIso {S : Scheme.{u}} {X Z B : AlgebraicSpace S} (f : X ⟶ Z)
    (g : Z ⟶ B) : smallFunctor f g ⋙ uliftFunctor.{u + 1, u} ≅
      restrictionOfScalars f g :=
  NatIso.ofComponents
    (fun T ↦ Equiv.toIso
      (Equiv.ulift.trans (equivShrink (Pair f g T.unop)).symm))
    sorry

/-- If `Z ⟶ B` is finite locally free, then the small functor of points of
`Res_{Z/B}(X)` is an algebraic space. -/
instance instIsAlgebraicSpace {S : Scheme.{u}} {X Z B : AlgebraicSpace S}
    (f : X ⟶ Z) (g : Z ⟶ B) [FiniteLocallyFree g] :
    IsAlgebraicSpace (smallFunctor f g) :=
  sorry

/-- The algebraic space `Res_{Z/B}(X)` over `S`. -/
def space {S : Scheme.{u}} {X Z B : AlgebraicSpace S} (f : X ⟶ Z) (g : Z ⟶ B)
    [FiniteLocallyFree g] : AlgebraicSpace S :=
  ofIsAlgebraicSpace (smallFunctor f g)

/-- The functor of points of `space f g` is `smallFunctor f g`. -/
theorem space_functorOfPoints {S : Scheme.{u}} {X Z B : AlgebraicSpace S}
    (f : X ⟶ Z) (g : Z ⟶ B) [FiniteLocallyFree g] :
    (space f g).functorOfPoints = smallFunctor f g :=
  sorry

/-- The universe-raised sheaf of points of `space f g` recovers
`restrictionOfScalarsSheaf f g`. -/
def spaceSheafIso {S : Scheme.{u}} {X Z B : AlgebraicSpace S} (f : X ⟶ Z)
    (g : Z ⟶ B) [FiniteLocallyFree g] :
    uliftSheaf (space f g) ≅ restrictionOfScalarsSheaf f g :=
  (fullyFaithfulSheafToPresheaf (Scheme.fppfTopology.over S) (Type (u + 1))).preimageIso
    (eqToIso (congrArg (fun F ↦ F ⋙ uliftFunctor.{u + 1, u})
        (space_functorOfPoints f g)) ≪≫
      smallFunctorUliftIso f g)

end AlgebraicGeometry.AlgebraicSpace.RestrictionOfScalars
