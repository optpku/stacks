/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.Noetherian
import StacksCheckRecall

/-!
# Lemma 87.20.5

A representable-by-algebraic-spaces morphism of affine formal algebraic spaces
that is surjective, flat, and locally of finite type transfers the Noetherian
type in both directions.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.ChosenBigFppfSite

noncomputable section

universe u

namespace AlgebraicGeometry

/- Lemma 87.20.5: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
affine formal algebraic spaces which is representable by algebraic spaces,
surjective, flat, and (locally) of finite type. Then `X` is Noetherian if and
only if `Y` is Noetherian. -/
@[stacks 0AKW] #check (AlgebraicGeometry.IsNoetherianAffine.iff_of_surjective_flat :
  ∀ {S : Scheme.{u}}
    [HasWeakSheafify (ChosenBigFppfSite.full.bigTopology S) (Type (u + 1))]
    [HasPullbacks (Sheaf (ChosenBigFppfSite.full.bigTopology S) (Type (u + 1)))]
    {X Y : Sheaf (ChosenBigFppfSite.full.bigTopology S) (Type (u + 1))}
    [IsAffineFormalAlgebraicSpace X] [IsAffineFormalAlgebraicSpace Y]
    {f : X ⟶ Y} (hf : ChosenBigFppfSite.representableByAlgebraicSpaces f)
    (h_surjective : (MorphismProperty.inverseImage (@Surjective : MorphismProperty Scheme)
        (ChosenBigFppfSite.full.bigToScheme S)).relative
      (ChosenBigFppfSite.full.bigTopology S).sheafifiedRepresentableFunctor f)
    (h_flat : (MorphismProperty.inverseImage (@Flat : MorphismProperty Scheme)
        (ChosenBigFppfSite.full.bigToScheme S)).relative
      (ChosenBigFppfSite.full.bigTopology S).sheafifiedRepresentableFunctor f)
    (h_locallyOfFiniteType : (MorphismProperty.inverseImage (@LocallyOfFiniteType)
        (ChosenBigFppfSite.full.bigToScheme S)).relative
      (ChosenBigFppfSite.full.bigTopology S).sheafifiedRepresentableFunctor f),
    IsNoetherianAffine X ↔ IsNoetherianAffine Y)

end AlgebraicGeometry
