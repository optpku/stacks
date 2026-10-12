/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Lemma_66_18_12_Comparison
public import stacks_project.Chap66.Lemma_66_18_12_Pushforward
public import stacks_project.Chap66.Lemma_66_18_12_Restriction

/-!
# Lemma 66.18.12

Étale base change of small étale pushforward and of higher direct images, for a
cartesian square of algebraic spaces with étale bottom edge.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImageEtaleBaseChangeHom` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of clause (2).
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Lemma 66.18.12 (1): for a cartesian square of algebraic spaces over a scheme `S` with étale
bottom edge `g : Y' ⟶ Y`, restriction of a sheaf `F` on `X_étale` along the étale edges
commutes with small étale pushforward, as sheaves on `Y'_étale`. -/
@[stacks 03LR]
instance isIso_pushforwardEtaleBaseChangeHom {X' X Y' Y : AlgebraicSpace S}
    {h : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (h_cart : IsPullback h f' f g) [Etale g] [Etale h]
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    IsIso (pushforwardEtaleBaseChangeHom h_cart (Type (u + 1)) F) :=
  sorry

/-- Lemma 66.18.12 (2): in the situation of (1), if `F` is an abelian sheaf then restriction
commutes with higher direct images `R^i f_small,*`. -/
@[stacks 03LR]
instance isIso_higherDirectImageEtaleBaseChangeHom {X' X Y' Y : AlgebraicSpace S}
    {h : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (h_cart : IsPullback h f' f g) [Etale g] [Etale h]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasSheafify (smallEtaleTopology X') AddCommGrpCat.{u + 1}]
    [HasSheafify (smallEtaleTopology Y) AddCommGrpCat.{u + 1}]
    [HasSheafify (smallEtaleTopology Y') AddCommGrpCat.{u + 1}]
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [Abelian (Sheaf (smallEtaleTopology X') AddCommGrpCat.{u + 1})]
    [Abelian (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
    [Abelian (Sheaf (smallEtaleTopology Y') AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X') AddCommGrpCat.{u + 1})]
    [(sheafPushforward AddCommGrpCat.{u + 1} f).Additive]
    [(sheafPushforward AddCommGrpCat.{u + 1} f').Additive]
    [(etaleRestrictionSheaf g AddCommGrpCat.{u + 1}).Additive]
    [(etaleRestrictionSheaf h AddCommGrpCat.{u + 1}).Additive]
    [(etaleRestrictionSheaf g AddCommGrpCat.{u + 1}).PreservesHomology]
    [(etaleRestrictionSheaf h AddCommGrpCat.{u + 1}).PreservesHomology]
    [(etaleRestrictionSheaf h AddCommGrpCat.{u + 1}).PreservesInjectiveObjects]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) (i : ℕ) :
    IsIso (higherDirectImageEtaleBaseChangeHom h_cart F i) :=
  sorry

/-- For a cartesian square with étale bottom edge, inverse image commutes with étale
restriction: `(f')_small^{-1}(G|_{Y'}) ≅ (f_small^{-1} G)|_{X'}`. -/
instance isIso_inverseImageEtaleRestrictHom {X' X Y' Y : AlgebraicSpace S}
    {h : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (h_cart : IsPullback h f' f g) [Etale g] [Etale h]
    [∀ F : (smallEtaleSite Y)ᵒᵖ ⥤ Type (u + 1),
      (etaleBaseChange f).op.HasLeftKanExtension F]
    [∀ F : (smallEtaleSite Y')ᵒᵖ ⥤ Type (u + 1),
      (etaleBaseChange f').op.HasLeftKanExtension F]
    [HasWeakSheafify (spacesEtaleTopology X) (Type (u + 1))]
    [HasWeakSheafify (spacesEtaleTopology X') (Type (u + 1))]
    (G : Sheaf (smallEtaleTopology Y) (Type (u + 1))) :
    IsIso (inverseImageEtaleRestrictHom h_cart (Type (u + 1)) G) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
