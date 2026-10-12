/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Logic.Small.Defs
public import stacks_project.Chap65.Lemma_65_16_4_IsAlgebraicSpace
public import stacks_project.Chap67.Definition_67_46_2_FiniteLocallyFree
public import stacks_project.Chap78.Definition_78_19_1_QuotientSheaf
public import stacks_project.Chap97.«97_10_0_2_Presheaf»
public import stacks_project.Chap97.Lemma_97_10_1_Sheaf

/-!
# Algebraic space of relative morphisms

If `Z ⟶ B` is finite locally free, the relative-Hom functor `Mor_B(Z, X)` is
represented by an algebraic space over `S`, obtained from the `u`-small encoding
of `HomPair`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeHom

namespace HomPair

/-- The type of relative-Hom pairs over a scheme `T` is `u`-small. -/
instance instSmall {S : Scheme.{u}} {B : AlgebraicSpace S} {Z X : Over B}
    (T : Over S) : Small.{u} (HomPair Z X T) :=
  sorry

end HomPair

/-- The `u`-small functor of points of `Mor_B(Z, X)`, sending `T` to a shrink of
the type of pairs `(a, b)`. -/
def smallFunctor {S : Scheme.{u}} {B : AlgebraicSpace S} (Z X : Over B) :
    (Over S)ᵒᵖ ⥤ Type u where
  obj T := Shrink (HomPair Z X T.unop)
  map {T T'} h :=
    TypeCat.ofHom fun p ↦
      equivShrink (HomPair Z X T'.unop)
        (HomPair.pullback h.unop ((equivShrink (HomPair Z X T.unop)).symm p))
  map_id := sorry
  map_comp := sorry

/-- Evaluating `smallFunctor Z X` at `T` recovers the shrink of `HomPair Z X T`. -/
theorem smallFunctor_obj {S : Scheme.{u}} {B : AlgebraicSpace S} (Z X : Over B)
    (T : Over S) : (smallFunctor Z X).obj (op T) = Shrink (HomPair Z X T) :=
  sorry

/-- Values of `smallFunctor Z X` are equivalent to relative-Hom pairs over `T`. -/
def smallFunctor_equiv {S : Scheme.{u}} {B : AlgebraicSpace S} (Z X : Over B)
    (T : Over S) : (smallFunctor Z X).obj (op T) ≃ HomPair Z X T :=
  (equivShrink (HomPair Z X T)).symm

/-- Universe lifting of `smallFunctor Z X` recovers the relative-Hom functor
`Mor_B(Z, X)`. -/
def smallFunctorUliftIso {S : Scheme.{u}} {B : AlgebraicSpace S} (Z X : Over B) :
    smallFunctor Z X ⋙ uliftFunctor.{u + 1, u} ≅ functor Z X :=
  NatIso.ofComponents
    (fun T ↦ Equiv.toIso
      (Equiv.ulift.trans (equivShrink (HomPair Z X T.unop)).symm))
    sorry

/-- If `Z ⟶ B` is finite locally free, then the small functor of points of
`Mor_B(Z, X)` is an algebraic space. -/
instance instIsAlgebraicSpace {S : Scheme.{u}} {B : AlgebraicSpace S}
    {Z X : Over B} [FiniteLocallyFree Z.hom] :
    IsAlgebraicSpace (smallFunctor Z X) :=
  sorry

/-- The algebraic space `Mor_B(Z, X)` over `S`. -/
def space {S : Scheme.{u}} {B : AlgebraicSpace S} (Z X : Over B)
    [FiniteLocallyFree Z.hom] : AlgebraicSpace S :=
  ofIsAlgebraicSpace (smallFunctor Z X)

/-- The functor of points of `space Z X` is `smallFunctor Z X`. -/
theorem space_functorOfPoints {S : Scheme.{u}} {B : AlgebraicSpace S}
    (Z X : Over B) [FiniteLocallyFree Z.hom] :
    (space Z X).functorOfPoints = smallFunctor Z X :=
  sorry

/-- The universe-raised sheaf of points of `space Z X` recovers `homSheaf Z X`. -/
def spaceSheafIso {S : Scheme.{u}} {B : AlgebraicSpace S} (Z X : Over B)
    [FiniteLocallyFree Z.hom] : uliftSheaf (space Z X) ≅ homSheaf Z X :=
  (fullyFaithfulSheafToPresheaf (Scheme.fppfTopology.over S) (Type (u + 1))).preimageIso
    (eqToIso (congrArg (fun F ↦ F ⋙ uliftFunctor.{u + 1, u})
        (space_functorOfPoints Z X)) ≪≫
      smallFunctorUliftIso Z X)

end AlgebraicGeometry.AlgebraicSpace.RelativeHom
