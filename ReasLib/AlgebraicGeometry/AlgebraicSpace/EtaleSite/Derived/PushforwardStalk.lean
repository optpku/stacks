/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Derived.Stalk
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Closed.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.UniversallyInjective

/-!
# Stalks of supported derived étale pushforwards

For a morphism of algebraic spaces, the derived étale stalk of a pushforward of an
object supported on an inverse image coincides with the stalk at the source geometric
point, provided the inverse-image morphism is integral and universally injective.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

-- Local instance justification (defeq pin): sheaf preadditive inference otherwise differs from the Abelian-induced structures fixed by DerivedCategory.Qh and exact-derived factorization; pin the existing canonical projections consistently for homotopy categories, additive binders, and derived models.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

namespace AlgebraicGeometry.AlgebraicSpace

/-- Let `S` be a scheme. Let `f : Y ⟶ X` be a morphism of algebraic spaces
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
