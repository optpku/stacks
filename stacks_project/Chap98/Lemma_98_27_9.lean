/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Separation
public import stacks_project.Chap98.Lemma_98_27_4_Functor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Closed-immersion diagonals of Artin contraction functors

In Situation 98.27.1, if `X' ⟶ S` and `W ⟶ S` are separated, then the
diagonal of the contraction functor on locally Noetherian schemes over `S`
is representable by closed immersions.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite Limits TypeCat
open CategoryTheory.ObjectProperty
open AlgebraicGeometry.Scheme.Over

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ContractionSituation

variable {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]

/-- The unique structure morphism from the formal algebraic space `W` to `S`. -/
def toBaseW (σ : ContractionSituation S) :
    σ.W ⟶ yoneda.obj (Over.mk (𝟙 S)) where
  app T := ofHom fun _ ↦ Over.homMk T.unop.hom
  naturality := sorry

/-- The component of `toBaseW σ` at `T` is the unique morphism
`T.unop ⟶ Over.mk (𝟙 S)`. -/
theorem toBaseW_app (σ : ContractionSituation S) (T : (Over S)ᵒᵖ)
    (x : σ.W.obj T) :
    (toBaseW σ).app T x = Over.homMk T.unop.hom :=
  sorry

/-- Any morphism from `W` to `S` as a scheme over itself equals `toBaseW`. -/
theorem eq_toBaseW {σ : ContractionSituation S}
    (f : σ.W ⟶ yoneda.obj (Over.mk (𝟙 S))) : f = toBaseW σ :=
  sorry

/-- A morphism of `Type (u + 1)` functors on locally Noetherian schemes over
`S` is a closed immersion when it is relatively representable with respect to
`uliftYoneda` and every represented pullback is a closed immersion of schemes. -/
def IsClosedImmersionOnLocallyNoetherian
    {F G : (locallyNoetherian S).FullSubcategoryᵒᵖ ⥤ Type (u + 1)}
    (φ : F ⟶ G) : Prop :=
  ((MorphismProperty.over
        (@AlgebraicGeometry.IsClosedImmersion : MorphismProperty Scheme.{u})).inverseImage
      (locallyNoetherian S).ι).relative uliftYoneda.{u + 1} φ

/-- Closed immersions of contraction-sized functors are relatively representable
`uliftYoneda` morphisms whose represented scheme maps are closed immersions. -/
theorem isClosedImmersionOnLocallyNoetherian_iff
    {F G : (locallyNoetherian S).FullSubcategoryᵒᵖ ⥤ Type (u + 1)}
    (φ : F ⟶ G) :
    IsClosedImmersionOnLocallyNoetherian φ ↔
      uliftYoneda.{u + 1}.relativelyRepresentable φ ∧
        ∀ ⦃V W : (locallyNoetherian S).FullSubcategory⦄
          (ξ : uliftYoneda.{u + 1}.obj V ⟶ G)
          (fst : uliftYoneda.{u + 1}.obj W ⟶ F) (snd : W ⟶ V),
          IsPullback fst (uliftYoneda.{u + 1}.map snd) φ ξ →
            AlgebraicGeometry.IsClosedImmersion snd.hom.left :=
  sorry

/-- Lemma 98.27.9: In Situation 98.27.1, if `X' ⟶ S` and `W ⟶ S` are
separated, then the diagonal `Limits.diag σ.functor` of the contraction
functor on locally Noetherian schemes over `S` is representable by closed
immersions. -/
@[stacks 0GHF]
theorem isClosedImmersion_diagonal (σ : ContractionSituation S)
    [Separated (toBase σ.X')] [FormalAlgebraicSpace.Separated (toBaseW σ)] :
    IsClosedImmersionOnLocallyNoetherian (Limits.diag σ.functor) :=
  sorry

/-- The diagonal of `σ.functor` is representable by closed immersions if and
only if it is `uliftYoneda`-relatively representable and every represented
pullback is a closed immersion of locally Noetherian schemes over `S`. -/
theorem isClosedImmersion_diagonal_iff (σ : ContractionSituation S)
    [Separated (toBase σ.X')] [FormalAlgebraicSpace.Separated (toBaseW σ)] :
    IsClosedImmersionOnLocallyNoetherian (Limits.diag σ.functor) ↔
      uliftYoneda.{u + 1}.relativelyRepresentable (Limits.diag σ.functor) ∧
        ∀ ⦃V W : (locallyNoetherian S).FullSubcategory⦄
          (ξ : uliftYoneda.{u + 1}.obj V ⟶ σ.functor ⨯ σ.functor)
          (fst : uliftYoneda.{u + 1}.obj W ⟶ σ.functor) (snd : W ⟶ V),
          IsPullback fst (uliftYoneda.{u + 1}.map snd)
              (Limits.diag σ.functor) ξ →
            AlgebraicGeometry.IsClosedImmersion snd.hom.left :=
  sorry

/-- The diagonal of the contraction functor is relatively representable with
respect to `uliftYoneda`. -/
theorem relativelyRepresentable_diagonal (σ : ContractionSituation S)
    [Separated (toBase σ.X')] [FormalAlgebraicSpace.Separated (toBaseW σ)] :
    uliftYoneda.{u + 1}.relativelyRepresentable (Limits.diag σ.functor) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ContractionSituation
