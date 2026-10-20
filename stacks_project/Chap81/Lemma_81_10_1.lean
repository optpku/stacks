/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Derived.PushforwardStalk
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

-- Local instance justification (defeq pin): sheaf preadditive inference otherwise differs from the Abelian-induced structures fixed by DerivedCategory.Qh and exact-derived factorization; pin the existing canonical projections consistently for homotopy categories, additive binders, and derived models.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

/- Lemma 81.10.1: the derived pushforward stalk of an object supported on the inverse
image of a closed subspace is the stalk at the source geometric point when the induced
morphism to the closed subspace is integral and universally injective. -/
@[stacks 0AEQ] #check (AlgebraicGeometry.AlgebraicSpace.etaleDerivedPushforward_stalk_iso :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
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
    (Q : EtaleDerived Y) (hQ : etaleDerivedSupportedOn (inverseImageι f i) Q),
    IsIsomorphic
      ((etaleDerivedStalk (ybar.map f)).obj (pushforwardModel.functor.obj Q))
      ((etaleDerivedStalk ybar).obj Q))
