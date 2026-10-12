/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_13_2_InverseImage
public import stacks_project.Chap67.Definition_67_45_2_Integral
public import stacks_project.Chap67.Lemma_67_19_5_UniversallyInjective
public import stacks_project.Chap69.Lemma_69_9_4_Pushforward
public import stacks_project.Chap81.Lemma_81_10_1_Stalk

/-!
# Lemma 81.10.1

For a morphism of algebraic spaces, the derived étale stalk of a pushforward of an
object supported on an inverse image coincides with the stalk at the source geometric
point, provided the inverse-image morphism is integral and universally injective.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 81.10.1: Let `S` be a scheme. Let `f : Y ⟶ X` be a morphism of algebraic spaces
over `S`. Let `i : Z ⟶ X` be a closed immersion such that `inverseImageTo f i` is integral
and universally injective. Let `ybar` be a geometric point of `Y`. For any
`Q : EtaleDerived Y` supported on `|inverseImage f i|`, the derived stalk of
`pushforwardModel.functor.obj Q` at `ybar.map f` is isomorphic in `D(Ab)` to the derived
stalk of `Q` at `ybar`. -/
@[stacks 0AEQ]
theorem etaleDerivedPushforward_stalk_iso {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i]
    [IsIntegralHom (inverseImageTo f i)] [UniversallyInjective (inverseImageTo f i)]
    [Etale (closedImmersionComplementι (inverseImageι f i))]
    [Abelian (EtaleSheaf X)] [Abelian (EtaleSheaf Y)]
    [Abelian (EtaleSheaf (closedImmersionComplement (inverseImageι f i)))]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasSheafify (smallEtaleTopology Y) AddCommGrpCat.{u + 1}]
    [HasDerivedCategory (EtaleSheaf X)] [HasDerivedCategory (EtaleSheaf Y)]
    [HasDerivedCategory AddCommGrpCat.{u + 1}]
    [(sheafPushforward AddCommGrpCat.{u + 1} f).Additive]
    (ybar : GeometricPoint Y)
    (pushforwardModel : EtaleRightDerivedModel (sheafPushforward AddCommGrpCat.{u + 1} f))
    (Q : EtaleDerived Y) (hQ : etaleDerivedSupportedOn (inverseImageι f i) Q) :
    IsIsomorphic
      ((etaleDerivedStalk (ybar.map f)).obj (pushforwardModel.functor.obj Q))
      ((etaleDerivedStalk ybar).obj Q) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
