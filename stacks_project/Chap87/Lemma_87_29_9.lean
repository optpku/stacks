module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.FiniteType
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.IsLocallyCountablyIndexed

universe u v

/- Lemma 87.29.9: Local finite type of a morphism of locally countably indexed
formal algebraic spaces is equivalent to taut topological finite type on all
étale affine-chart squares, on a target cover and covers of its pullbacks,
and on a source cover factoring through affine étale target charts. -/
@[stacks 0ANW] #check
  (AlgebraicGeometry.IsLocallyCountablyIndexed.locallyOfFiniteType_tfae :
    ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
      [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
      [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
      {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
      [IsLocallyCountablyIndexed X] [IsLocallyCountablyIndexed Y]
      (f : X ⟶ Y) [Fact (ChosenBigSite.IsSizeClosed 𝒮)],
      List.TFAE
        [etaleAffineLocally (fun φ => φ.IsTaut ∧ φ.TopologicallyOfFiniteType) f,
          existsCoverOnTarget (fun φ => φ.IsTaut ∧ φ.TopologicallyOfFiniteType) f,
          existsCoverOnSource (fun φ => φ.IsTaut ∧ φ.TopologicallyOfFiniteType) f,
          AlgebraicGeometry.IsLocallyCountablyIndexed.LocallyOfFiniteType f])
