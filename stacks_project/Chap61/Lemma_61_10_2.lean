/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.V.ProH
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open AffineFamilyOver

universe u

/- Lemma 61.10.2: for a morphism of affine schemes, the singleton family
{X → Y} is a standard V covering if and only if X is a directed inverse
limit of affine schemes over Y whose stage morphisms are singleton ph
coverings, if and only if the same holds with singleton h coverings. -/
@[stacks 0EVP] #check
  (AlgebraicGeometry.AffineFamilyOver.isStandardVCover_singleton_tfae :
    ∀ {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y),
      List.TFAE [IsStandardVCover (singleton f inferInstance),
        IsDirectedPhCover f, IsDirectedHCover f])

#check
  (AlgebraicGeometry.AffineFamilyOver.isStandardVCover_iff_isDirectedPhCover :
    ∀ {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y),
      IsStandardVCover (singleton f inferInstance) ↔ IsDirectedPhCover f)

#check
  (AlgebraicGeometry.AffineFamilyOver.isStandardVCover_iff_isDirectedHCover :
    ∀ {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y),
      IsStandardVCover (singleton f inferInstance) ↔ IsDirectedHCover f)
