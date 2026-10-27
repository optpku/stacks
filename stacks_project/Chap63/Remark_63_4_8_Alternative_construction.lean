/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Separated
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.LocallyQuasiFinite.Cech.Stalk
import StacksCheckRecall

/-!
# Alternative construction of locally quasi-finite lower shriek

The canonical affine cover `X.affineCover` gives the open family
`fun i ↦ (X.affineCover.f i).opensRange`. It covers by
`Scheme.OpenCover.isOpenCover_opensRange`, its members are affine by
`isAffineOpen_opensRange`, and its restrictions over any target are separated
by `Scheme.OpenCover.isSeparated_opensRange_comp`.
-/

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale
open AlgebraicGeometry.Scheme.GeometricPoint
open TopologicalSpace

universe u

/- Remark 63.4.8 (Alternative construction) (1): For a locally quasi-finite
morphism in the Stacks convention, a covering by opens with separated
restrictions identifies lower shriek with the cokernel of the signed separated
Čech map from ordered-pair summands to singleton summands. -/
@[stacks 0F5I]
#check (AlgebraicGeometry.Scheme.Etale.lowerShriekCechCokernelIso :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f] [LocallyOfFiniteType f]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    [HasCoproducts.{u} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
    {ι : Type u} (𝒰 : ι → X.Opens) [∀ i, IsSeparated ((𝒰 i).ι ≫ f)]
    (h𝒰 : IsOpenCover 𝒰), lowerShriekCechCokernelFunctor f 𝒰 ≅ lowerShriek f)

/- Remark 63.4.8 (Alternative construction) (2): Computing the alternative
construction's stalks from the separated stalk formula gives the coproduct of
stalks over same-field geometric lifts, as in Lemma 63.4.5. -/
@[stacks 0F5I]
#check (AlgebraicGeometry.Scheme.Etale.lowerShriekCechCokernelStalkIso :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f] [LocallyOfFiniteType f]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    [HasCoproducts.{u} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
    {ι : Type u} (𝒰 : ι → X.Opens) [∀ i, IsSeparated ((𝒰 i).ι ≫ f)]
    (h𝒰 : IsOpenCover 𝒰) (ybar : GeometricPoint Y),
    lowerShriekCechCokernelFunctor f 𝒰 ⋙ (toSmallEtalePoint ybar).sheafFiber ≅
      abelianStalkCoproduct f ybar)
