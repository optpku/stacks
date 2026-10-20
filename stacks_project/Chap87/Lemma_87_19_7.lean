module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.AffineMorphism
import StacksCheckRecall

/-!
# Lemma 87.19.7

A morphism of affine formal algebraic spaces that is representable by
algebraic spaces is representable by schemes and affine.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.ChosenBigFppfSite

noncomputable section

universe u v

open AlgebraicGeometry

/- Lemma 87.19.7: Let `S` be a scheme. A morphism `f : X ⟶ Y` of affine
formal algebraic spaces that is representable by algebraic spaces is
representable by schemes and affine. -/
@[stacks 0AKN] #check (AlgebraicGeometry.IsAffineFormalAlgebraicSpace.isAffineHom_relative :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsAffineFormalAlgebraicSpace X] [IsAffineFormalAlgebraicSpace Y]
    {f : X ⟶ Y} (hf : representableByAlgebraicSpaces f),
    (MorphismProperty.inverseImage (@IsAffineHom) (𝒮.bigToScheme S)).relative
      (𝒮.bigTopology S).sheafifiedRepresentableFunctor f)
