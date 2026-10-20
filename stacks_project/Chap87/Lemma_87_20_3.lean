module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.FlatDescent

/-!
# Lemma 87.20.3

A representable-by-algebraic-spaces morphism of affine formal algebraic spaces
that is surjective and flat transfers the weakly adic type in both directions.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.ChosenBigFppfSite

noncomputable section

universe u v

namespace AlgebraicGeometry

/- Lemma 87.20.3: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
affine formal algebraic spaces which is representable by algebraic spaces,
surjective, and flat. Then `X` is weakly adic if and only if `Y` is weakly
adic. -/
@[stacks 0GXS] #check (AlgebraicGeometry.IsWeaklyAdicAffine.iff_of_surjective_flat :
    ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
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
      (𝒮.bigTopology S).sheafifiedRepresentableFunctor f),
    IsWeaklyAdicAffine X ↔ IsWeaklyAdicAffine Y)

end AlgebraicGeometry
