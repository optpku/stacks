module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.Taut
import StacksCheckRecall

/-!
# Taut charts and representability by algebraic spaces

Lemma 87.22.2 records that a morphism of locally countably indexed formal
algebraic spaces is representable by algebraic spaces if and only if its
étale affine charts, or some Definition 87.11.1 covering of the target or of
the source, correspond to taut maps of `WAdm^count`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ChosenBigFppfSite TopologicalRing

universe u v

open AlgebraicGeometry.IsLocallyCountablyIndexed

/- Lemma 87.22.2: Taut affine étale-chart testing, taut target-cover testing,
taut source-cover testing, and representability by algebraic spaces are
equivalent for morphisms of locally countably indexed formal algebraic spaces. -/
@[stacks 0ANK] #check (AlgebraicGeometry.IsLocallyCountablyIndexed.isTaut_tfae :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsLocallyCountablyIndexed X] [IsLocallyCountablyIndexed Y]
    (f : X ⟶ Y) [Fact (ChosenBigSite.IsSizeClosed 𝒮)],
    List.TFAE [etaleAffineLocally (fun φ => φ.IsTaut) f,
      existsCoverOnTarget (fun φ => φ.IsTaut) f,
      existsCoverOnSource (fun φ => φ.IsTaut) f,
      representableByAlgebraicSpaces f])
