/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap110.Lemma_110_53_1
public import stacks_project.Chap99.Lemma_99_15_12_Inclusion

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

namespace AlgebraicGeometry.AlgebraicSpace.Spaces
namespace CurvesGroupoids

/-- Lemma 99.15.12: the 1-morphism (99.15.1.1) `CurvesGroupoids.inclusion`,
packaged as `inclusionHom`, is representable by open and closed immersions. -/
@[stacks 0D5B]
theorem inclusion_isOpenAndClosedImmersion (S : Scheme.{u}) :
    Classifying.relativelyRepresentableByAlgebraicSpaces (inclusionHom S) ∧
      ∀ ⦃U : Over S⦄ (y : Classifying.slice U ⟶ FpFlatProperGroupoids.toGroupoids S)
        (Fy : AlgebraicSpace S) (fy : Fy ⟶ ofOver U),
        Classifying.RepresentsBaseChange (inclusionHom S) y Fy fy →
          AlgebraicSpace.IsOpenImmersion fy ∧ AlgebraicSpace.IsClosedImmersion fy :=
  sorry

/-- Because (99.15.1.1) is fully faithful, representability by open and closed
immersions is the existence, for every fp-flat-proper family, of a clopen of
the base scheme through which a test morphism factors if and only if the base
change has relative dimension at most `1`. -/
theorem exists_isClopen_relativeDimensionLE (S : Scheme.{u})
    (P : FpFlatProperGroupoids S) :
    ∃ U : ((pFpFlatProperGroupoids S).obj P).left.Opens,
      IsClopen (U : Set ((pFpFlatProperGroupoids S).obj P).left) ∧
        ∀ {T : Over S} (h : T ⟶ (pFpFlatProperGroupoids S).obj P),
          Nonempty (Over.mk h.left ⟶ Over.mk U.ι) ↔
            RelativeDimensionLE (pullback.snd P.obj.obj.obj.hom (ofOverMap h)) 1 :=
  sorry

end CurvesGroupoids
end AlgebraicGeometry.AlgebraicSpace.Spaces
