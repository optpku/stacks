/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Definition_87_9_1_Affine
public import stacks_project.Chap87.Lemma_87_10_3_Types

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

universe u v

namespace AlgebraicGeometry

/-- Lemma 87.20.5: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
affine formal algebraic spaces which is representable by algebraic spaces,
surjective, flat, and (locally) of finite type. Then `X` is Noetherian if and
only if `Y` is Noetherian. -/
@[stacks 0AKW]
theorem IsNoetherianAffine.iff_of_surjective_flat
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsAffineFormalAlgebraicSpace X] [IsAffineFormalAlgebraicSpace Y]
    {f : X ⟶ Y} (hf : representableByAlgebraicSpaces f)
    (h_surjective : (MorphismProperty.inverseImage (@Surjective : MorphismProperty Scheme)
        (𝒮.bigToScheme S)).relative
      (𝒮.bigTopology S).sheafifiedRepresentableFunctor f)
    (h_flat : (MorphismProperty.inverseImage (@Flat : MorphismProperty Scheme)
        (𝒮.bigToScheme S)).relative
      (𝒮.bigTopology S).sheafifiedRepresentableFunctor f)
    (h_locallyOfFiniteType : (MorphismProperty.inverseImage (@LocallyOfFiniteType)
        (𝒮.bigToScheme S)).relative
      (𝒮.bigTopology S).sheafifiedRepresentableFunctor f) :
    IsNoetherianAffine X ↔ IsNoetherianAffine Y :=
  sorry

end AlgebraicGeometry
