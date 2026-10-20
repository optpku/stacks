module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.AdicStarLocalMorphismProperty
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.FiniteType

/-!
# Local finite type of locally adic-star formal algebraic spaces

Local finite type is characterized by adic topologically finite-type maps on
affine étale charts on a size-closed chosen big fppf site.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ChosenBigFppfSite TopologicalRing RingHom

namespace AlgebraicGeometry.IsLocallyAdicStar

variable {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
variable [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
variable [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
variable {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
variable [IsLocallyAdicStar X] [IsLocallyAdicStar Y]

/-- For a morphism of locally adic-star formal algebraic spaces on a size-closed
chosen big fppf site, local finite type is equivalent to adic topological finite
type on every affine étale square, on an affine étale target cover and affine
étale covers of its pullbacks, or on an affine étale source cover factoring
through affine étale target charts. -/
theorem locallyOfFiniteType_tfae (f : X ⟶ Y)
    [Fact (ChosenBigSite.IsSizeClosed 𝒮)] :
    List.TFAE
      [etaleAffineLocally (fun φ ↦ φ.IsAdicHom ∧ φ.TopologicallyOfFiniteType) f,
        existsCoverOnTarget (fun φ ↦ φ.IsAdicHom ∧ φ.TopologicallyOfFiniteType) f,
        existsCoverOnSource (fun φ ↦ φ.IsAdicHom ∧ φ.TopologicallyOfFiniteType) f,
        IsLocallyCountablyIndexed.LocallyOfFiniteType f] :=
  sorry

/-- A morphism of locally adic-star formal algebraic spaces is locally of finite
type if and only if every affine étale-chart square corresponds to an adic
topologically finite-type ring homomorphism. -/
theorem etaleAffineLocally_iff_locallyOfFiniteType (f : X ⟶ Y)
    [Fact (ChosenBigSite.IsSizeClosed 𝒮)] :
    etaleAffineLocally (fun φ ↦ φ.IsAdicHom ∧ φ.TopologicallyOfFiniteType) f ↔
      IsLocallyCountablyIndexed.LocallyOfFiniteType f :=
  (locallyOfFiniteType_tfae f).out 0 3

/-- A morphism of locally adic-star formal algebraic spaces is locally of finite
type if and only if it admits an affine étale target cover and affine étale
covers of its pullbacks whose maps to the target charts correspond to adic
topologically finite-type ring homomorphisms. -/
theorem existsCoverOnTarget_iff_locallyOfFiniteType (f : X ⟶ Y)
    [Fact (ChosenBigSite.IsSizeClosed 𝒮)] :
    existsCoverOnTarget (fun φ ↦ φ.IsAdicHom ∧ φ.TopologicallyOfFiniteType) f ↔
      IsLocallyCountablyIndexed.LocallyOfFiniteType f :=
  (locallyOfFiniteType_tfae f).out 1 3

/-- A morphism of locally adic-star formal algebraic spaces is locally of finite
type if and only if it admits an affine étale source cover factoring through
affine étale target charts by morphisms corresponding to adic topologically
finite-type ring homomorphisms. -/
theorem existsCoverOnSource_iff_locallyOfFiniteType (f : X ⟶ Y)
    [Fact (ChosenBigSite.IsSizeClosed 𝒮)] :
    existsCoverOnSource (fun φ ↦ φ.IsAdicHom ∧ φ.TopologicallyOfFiniteType) f ↔
      IsLocallyCountablyIndexed.LocallyOfFiniteType f :=
  (locallyOfFiniteType_tfae f).out 2 3

end AlgebraicGeometry.IsLocallyAdicStar
