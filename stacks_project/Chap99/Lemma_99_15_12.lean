module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Inclusion
import StacksCheckRecall

/-!
# Lemma 99.15.12

The 1-morphism (99.15.1.1) from the stack of curves to
`Spaces'_{fp, flat, proper}` is representable by open and closed immersions.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Spaces
open AlgebraicGeometry.GroupScheme
open CategoryTheory.Limits
open FiberedCategoryOver
open scoped Bicategory

noncomputable section

universe u

/- Lemma 99.15.12: the canonical 1-morphism (99.15.1.1) from curves to
finitely presented, flat, proper families is representable by open and closed
immersions. -/
@[stacks 0D5B] #check
  (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.inclusion_isOpenAndClosedImmersion :
    ∀ (S : Scheme.{u}),
    Classifying.relativelyRepresentableByAlgebraicSpaces (Curves.inclusionHom S) ∧
      ∀ ⦃U : Over S⦄ (y : Classifying.slice U ⟶ FpFlatProperGroupoids.toGroupoids S)
        (Fy : AlgebraicSpace S) (fy : Fy ⟶ ofOver U),
        Classifying.RepresentsBaseChange (Curves.inclusionHom S) y Fy fy →
          AlgebraicSpace.IsOpenImmersion fy ∧ AlgebraicSpace.IsClosedImmersion fy)

#check
  (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.exists_isClopen_relativeDimensionLE :
    ∀ (S : Scheme.{u}) (P : FpFlatProperGroupoids S),
    ∃ U : ((pFpFlatProperGroupoids S).obj P).left.Opens,
      IsClopen (U : Set ((pFpFlatProperGroupoids S).obj P).left) ∧
        ∀ {T : Over S} (h : T ⟶ (pFpFlatProperGroupoids S).obj P),
          Nonempty (Over.mk h.left ⟶ Over.mk U.ι) ↔
            RelativeDimensionLE (pullback.snd P.obj.obj.obj.hom (ofOverMap h)) 1)
