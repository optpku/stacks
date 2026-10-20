/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.LocalTypes
import StacksCheckRecall

@[expose] public section

universe u v

/- Definition 87.20.7 (1): for a scheme `S` and a formal algebraic space `X`
over `S`, we say `X` is locally countably indexed if the equivalent
conditions of Lemma 87.20.6 hold for the countably indexed affine type. -/
@[stacks 0AKY] #check (AlgebraicGeometry.IsLocallyCountablyIndexed :
  ∀ {𝒮 : AlgebraicGeometry.ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [CategoryTheory.HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [CategoryTheory.Limits.HasPullbacks
      (CategoryTheory.Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : CategoryTheory.Sheaf (𝒮.bigTopology S) (Type (max u v))), Prop)

/- Definition 87.20.7 (2): for a scheme `S` and a formal algebraic space `X`
over `S`, we say `X` is locally countably indexed and classical if the
equivalent conditions of Lemma 87.20.6 hold for the corresponding affine
type. -/
@[stacks 0AKY] #check (AlgebraicGeometry.IsLocallyClassical :
  ∀ {𝒮 : AlgebraicGeometry.ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [CategoryTheory.HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [CategoryTheory.Limits.HasPullbacks
      (CategoryTheory.Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : CategoryTheory.Sheaf (𝒮.bigTopology S) (Type (max u v))), Prop)

/- Definition 87.20.7 (3): for a scheme `S` and a formal algebraic space `X`
over `S`, we say `X` is locally weakly adic if the equivalent conditions of
Lemma 87.20.6 hold for the weakly adic affine type. -/
@[stacks 0AKY] #check (AlgebraicGeometry.IsLocallyWeaklyAdic :
  ∀ {𝒮 : AlgebraicGeometry.ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [CategoryTheory.HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [CategoryTheory.Limits.HasPullbacks
      (CategoryTheory.Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : CategoryTheory.Sheaf (𝒮.bigTopology S) (Type (max u v))), Prop)

/- Definition 87.20.7 (4): for a scheme `S` and a formal algebraic space `X`
over `S`, we say `X` is locally adic* if the equivalent conditions of
Lemma 87.20.6 hold for the adic* affine type. -/
@[stacks 0AKY] #check (AlgebraicGeometry.IsLocallyAdicStar :
  ∀ {𝒮 : AlgebraicGeometry.ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [CategoryTheory.HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [CategoryTheory.Limits.HasPullbacks
      (CategoryTheory.Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : CategoryTheory.Sheaf (𝒮.bigTopology S) (Type (max u v))), Prop)

/- Definition 87.20.7 (5): for a scheme `S` and a formal algebraic space `X`
over `S`, we say `X` is locally Noetherian if the equivalent conditions of
Lemma 87.20.6 hold for the Noetherian affine type. -/
@[stacks 0AKY] #check (AlgebraicGeometry.IsFormalAlgebraicSpace.IsLocallyNoetherian :
  ∀ {𝒮 : AlgebraicGeometry.ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [CategoryTheory.HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [CategoryTheory.Limits.HasPullbacks
      (CategoryTheory.Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : CategoryTheory.Sheaf (𝒮.bigTopology S) (Type (max u v))), Prop)
