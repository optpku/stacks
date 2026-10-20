module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.Diagonal
import StacksCheckRecall

/-!
# Lemma 87.15.5

The relative diagonal of a morphism of formal algebraic spaces is representable,
a monomorphism, locally quasi-finite, locally of finite type, and separated, as a
representable transformation of fppf sheaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry
open AlgebraicGeometry.ChosenBigFppfSite

universe u v

/- Lemma 87.15.5: The relative diagonal of a morphism of formal algebraic spaces
is representable, a monomorphism, locally quasi-finite, locally of finite type,
and separated. -/
@[stacks 0AN2] #check
  (AlgebraicGeometry.IsFormalAlgebraicSpace.relativeDiagonal_properties :
    ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] (f : X ⟶ Y),
    (𝒮.bigTopology S).sheafifiedRepresentableFunctor.relativelyRepresentable
      (pullback.diagonal f) ∧
      (MorphismProperty.inverseImage (MorphismProperty.monomorphisms Scheme)
          (𝒮.bigToScheme S)).relative
        (𝒮.bigTopology S).sheafifiedRepresentableFunctor (pullback.diagonal f) ∧
      (MorphismProperty.inverseImage (@LocallyQuasiFinite) (𝒮.bigToScheme S)).relative
        (𝒮.bigTopology S).sheafifiedRepresentableFunctor (pullback.diagonal f) ∧
      (MorphismProperty.inverseImage (@LocallyOfFiniteType) (𝒮.bigToScheme S)).relative
        (𝒮.bigTopology S).sheafifiedRepresentableFunctor (pullback.diagonal f) ∧
      (MorphismProperty.inverseImage (@IsSeparated) (𝒮.bigToScheme S)).relative
        (𝒮.bigTopology S).sheafifiedRepresentableFunctor (pullback.diagonal f))
