module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.Diagonal
import StacksCheckRecall

/-!
# Lemma 87.9.2

The diagonal of an affine formal algebraic space is representable and a closed
immersion in the sense of a representable transformation of fppf sheaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.ChosenBigFppfSite

noncomputable section

universe u v

open AlgebraicGeometry

/- Lemma 87.9.2: The diagonal of an affine formal algebraic space is
representable and a closed immersion. -/
@[stacks 0AI8] #check (AlgebraicGeometry.IsAffineFormalAlgebraicSpace.isClosedImmersion_diag :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAffineFormalAlgebraicSpace X],
    (MorphismProperty.inverseImage (@IsClosedImmersion) (𝒮.bigToScheme S)).relative
      (𝒮.bigTopology S).sheafifiedRepresentableFunctor (diag X))

#check (AlgebraicGeometry.IsAffineFormalAlgebraicSpace.relativelyRepresentable_diag :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAffineFormalAlgebraicSpace X],
    (𝒮.bigTopology S).sheafifiedRepresentableFunctor.relativelyRepresentable (diag X))

#check (AlgebraicGeometry.IsAffineFormalAlgebraicSpace.isClosedImmersion_diag_spec :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAffineFormalAlgebraicSpace X],
    (𝒮.bigTopology S).sheafifiedRepresentableFunctor.relativelyRepresentable (diag X) ∧
      ∀ {U V : 𝒮.bigSite S}
        (ξ : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ X ⨯ X)
        (fst : (𝒮.bigTopology S).sheafifiedRepresentable V ⟶ X) (snd : V ⟶ U),
        IsPullback fst ((𝒮.bigTopology S).sheafifiedRepresentableMap snd) (diag X) ξ →
          IsClosedImmersion ((𝒮.bigToScheme S).map snd))
