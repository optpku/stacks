/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.AffineAscent
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry

universe u v

/- Lemma 87.19.9 (1): Let `S` be a scheme. Let `Y` be an affine formal
algebraic space. Let `f : X ⟶ Y` be a map of sheaves on `(Sch/S)_fppf` which
is representable and affine. Then `X` is an affine formal algebraic space. -/
@[stacks 0AKP] #check (AlgebraicGeometry.IsAffineFormalAlgebraicSpace.of_relativelyAffine :
  ∀
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsAffineFormalAlgebraicSpace Y] {f : X ⟶ Y} (hf : relativelyAffine f),
    IsAffineFormalAlgebraicSpace X)

/- Lemma 87.19.9 (2): Let `S` be a scheme. Let `Y` be an affine formal
algebraic space. Let `f : X ⟶ Y` be a map of sheaves on `(Sch/S)_fppf` which
is representable and affine. If `Y` is countably indexed, then `X` is
countably indexed. -/
@[stacks 0AKP] #check (AlgebraicGeometry.IsCountablyIndexedAffine.of_relativelyAffine :
  ∀
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsCountablyIndexedAffine Y] {f : X ⟶ Y} (hf : relativelyAffine f),
    IsCountablyIndexedAffine X)

/- Lemma 87.19.9 (3): Let `S` be a scheme. Let `Y` be an affine formal
algebraic space. Let `f : X ⟶ Y` be a map of sheaves on `(Sch/S)_fppf` which
is representable and affine. If `Y` is countably indexed and classical, then
`X` is countably indexed and classical. -/
@[stacks 0AKP] #check (AlgebraicGeometry.IsClassicalAffine.of_relativelyAffine :
  ∀
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsCountablyIndexedAffine Y] [IsClassicalAffine Y]
    {f : X ⟶ Y} (hf : relativelyAffine f),
    IsCountablyIndexedAffine X ∧ IsClassicalAffine X)

/- Lemma 87.19.9 (4): Let `S` be a scheme. Let `Y` be an affine formal
algebraic space. Let `f : X ⟶ Y` be a map of sheaves on `(Sch/S)_fppf` which
is representable and affine. If `Y` is weakly adic, then `X` is weakly adic. -/
@[stacks 0AKP] #check (AlgebraicGeometry.IsWeaklyAdicAffine.of_relativelyAffine :
  ∀
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsWeaklyAdicAffine Y] {f : X ⟶ Y} (hf : relativelyAffine f),
    IsWeaklyAdicAffine X)

/- Lemma 87.19.9 (5): Let `S` be a scheme. Let `Y` be an affine formal
algebraic space. Let `f : X ⟶ Y` be a map of sheaves on `(Sch/S)_fppf` which
is representable and affine. If `Y` is adic*, then `X` is adic*. -/
@[stacks 0AKP] #check (AlgebraicGeometry.IsAdicStar.of_relativelyAffine :
  ∀
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsAdicStar Y] {f : X ⟶ Y} (hf : relativelyAffine f),
    IsAdicStar X)

/- Lemma 87.19.9 (6): Let `S` be a scheme. Let `Y` be an affine formal
algebraic space. Let `f : X ⟶ Y` be a map of sheaves on `(Sch/S)_fppf` which
is representable and affine. If `Y` is Noetherian and `f` is locally of finite
type, then `X` is Noetherian. -/
@[stacks 0AKP] #check (AlgebraicGeometry.IsNoetherianAffine.of_relativelyAffine :
  ∀
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsNoetherianAffine Y] {f : X ⟶ Y} (hf : relativelyAffine f)
    (hft : (MorphismProperty.inverseImage (@LocallyOfFiniteType)
        (𝒮.bigToScheme S)).relative
      (𝒮.bigTopology S).sheafifiedRepresentableFunctor f),
    IsNoetherianAffine X)

