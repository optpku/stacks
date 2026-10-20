module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.LocalMorphismProperty
public import ReasLib.Topology.Algebra.Ring.Taut

/-!
# Taut charts and representability by algebraic spaces

On a size-closed chosen fppf site, representability of morphisms of locally
countably indexed formal algebraic spaces is characterized by taut affine
étale charts.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ChosenBigFppfSite TopologicalRing

universe u v

namespace AlgebraicGeometry.IsLocallyCountablyIndexed

variable {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
variable [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
variable [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
variable {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}

/-- On a size-closed chosen fppf site, a morphism of locally countably indexed
formal algebraic spaces is representable by algebraic spaces if and only if
every affine étale-chart square has top arrow corresponding to a taut ring map,
if and only if there is an affine étale target cover with affine étale covers
of its pullbacks whose projections correspond to taut ring maps, if and only if
there is an affine étale source cover factoring through affine étale target
charts by morphisms corresponding to taut ring maps. -/
theorem isTaut_tfae
    [IsLocallyCountablyIndexed X] [IsLocallyCountablyIndexed Y]
    (f : X ⟶ Y) [Fact (ChosenBigSite.IsSizeClosed 𝒮)] :
    List.TFAE [etaleAffineLocally (fun φ => φ.IsTaut) f,
      existsCoverOnTarget (fun φ => φ.IsTaut) f,
      existsCoverOnSource (fun φ => φ.IsTaut) f,
      representableByAlgebraicSpaces f] := sorry

/-- On a size-closed chosen fppf site, representability by algebraic spaces is
equivalent to tautness on every affine étale-chart square of a morphism of
locally countably indexed formal algebraic spaces. -/
theorem etaleAffineLocally_isTaut_iff
    [IsLocallyCountablyIndexed X] [IsLocallyCountablyIndexed Y]
    (f : X ⟶ Y) [Fact (ChosenBigSite.IsSizeClosed 𝒮)] :
    etaleAffineLocally (fun φ => φ.IsTaut) f ↔ representableByAlgebraicSpaces f :=
  (isTaut_tfae f).out 0 3

/-- On a size-closed chosen fppf site, a morphism of locally countably indexed
formal algebraic spaces is representable by algebraic spaces if and only if
there is an affine étale target cover and affine étale covers of its pullbacks
whose projections to the target charts correspond to taut ring maps. -/
theorem existsCoverOnTarget_isTaut_iff
    [IsLocallyCountablyIndexed X] [IsLocallyCountablyIndexed Y]
    (f : X ⟶ Y) [Fact (ChosenBigSite.IsSizeClosed 𝒮)] :
    existsCoverOnTarget (fun φ => φ.IsTaut) f ↔ representableByAlgebraicSpaces f :=
  (isTaut_tfae f).out 1 3

/-- On a size-closed chosen fppf site, a morphism of locally countably indexed
formal algebraic spaces is representable by algebraic spaces if and only if
there is an affine étale source cover factoring through affine étale target
charts by morphisms corresponding to taut ring maps. -/
theorem existsCoverOnSource_isTaut_iff
    [IsLocallyCountablyIndexed X] [IsLocallyCountablyIndexed Y]
    (f : X ⟶ Y) [Fact (ChosenBigSite.IsSizeClosed 𝒮)] :
    existsCoverOnSource (fun φ => φ.IsTaut) f ↔ representableByAlgebraicSpaces f :=
  (isTaut_tfae f).out 2 3

end AlgebraicGeometry.IsLocallyCountablyIndexed
