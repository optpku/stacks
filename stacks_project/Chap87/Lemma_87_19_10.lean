/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.TypeAscent

/-!
# Lemma 87.19.10

Countably indexed, classical, weakly adic, adic*, and Noetherian types ascend
along a morphism of affine formal algebraic spaces that is representable by
algebraic spaces.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.ChosenBigFppfSite

noncomputable section

universe u v

namespace AlgebraicGeometry

/- Lemma 87.19.10 (1): Countable indexing ascends along representable morphisms.
This theorem also supplies countability in the second source clause. -/
@[stacks 0AKQ] #check (AlgebraicGeometry.IsCountablyIndexedAffine.of_representableByAlgebraicSpaces :
    ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsAffineFormalAlgebraicSpace X] [IsCountablyIndexedAffine Y]
    {f : X ⟶ Y} (hf : representableByAlgebraicSpaces f),
    IsCountablyIndexedAffine X)

/- Lemma 87.19.10 (2): Classicality ascends from a countably indexed classical
target. Together with the first check, this gives countably indexed classical source. -/
@[stacks 0AKQ] #check (AlgebraicGeometry.IsClassicalAffine.of_representableByAlgebraicSpaces :
    ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsAffineFormalAlgebraicSpace X] [IsCountablyIndexedAffine Y]
    [IsClassicalAffine Y] {f : X ⟶ Y} (hf : representableByAlgebraicSpaces f),
    IsClassicalAffine X)

/- Lemma 87.19.10 (3): Weak adicity ascends along representable morphisms. -/
@[stacks 0AKQ] #check (AlgebraicGeometry.IsWeaklyAdicAffine.of_representableByAlgebraicSpaces :
    ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsAffineFormalAlgebraicSpace X] [IsWeaklyAdicAffine Y]
    {f : X ⟶ Y} (hf : representableByAlgebraicSpaces f),
    IsWeaklyAdicAffine X)

/- Lemma 87.19.10 (4): Adic* ascends along representable morphisms. -/
@[stacks 0AKQ] #check (AlgebraicGeometry.IsAdicStar.of_representableByAlgebraicSpaces :
    ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsAffineFormalAlgebraicSpace X] [IsAdicStar Y]
    {f : X ⟶ Y} (hf : representableByAlgebraicSpaces f),
    IsAdicStar X)

/- Lemma 87.19.10 (5): Noetherianity ascends along representable morphisms
that are locally of finite type. -/
@[stacks 0AKQ] #check (AlgebraicGeometry.IsNoetherianAffine.of_representableByAlgebraicSpaces :
    ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsAffineFormalAlgebraicSpace X] [IsNoetherianAffine Y]
    {f : X ⟶ Y} (hf : representableByAlgebraicSpaces f)
    (hft : (MorphismProperty.inverseImage (@LocallyOfFiniteType)
        (𝒮.bigToScheme S)).relative
      (𝒮.bigTopology S).sheafifiedRepresentableFunctor f),
    IsNoetherianAffine X)

end AlgebraicGeometry
