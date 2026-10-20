module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.AdicStarLocalMorphismProperty
public import ReasLib.RingTheory.Topology.AdicStar.Cancellation

/-!
# Cancellation of local morphism properties of locally adic-star spaces

Local properties of continuous homomorphisms of adic-star rings with cancellation
cancel along postcomposition of morphisms of locally adic-star formal algebraic
spaces on a size-closed chosen big fppf site.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ChosenBigFppfSite TopologicalRing

universe u v

namespace AlgebraicGeometry.IsLocallyAdicStar

variable {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
variable [hSheafify : HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
variable [hPullbacks : HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
variable {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
variable [hX : IsLocallyAdicStar X] [hY : IsLocallyAdicStar Y]
    [hZ : IsLocallyAdicStar Z]
variable (P : ∀ {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicStarRing A]
    [CommRing B] [TopologicalSpace B] [IsAdicStarRing B],
    (B →+* A) → Prop)
variable (f : X ⟶ Y) (g : Y ⟶ Z)

include hSheafify hPullbacks hX hY hZ

/-- Universal affine étale testing of a local property of continuous homomorphisms
of adic-star rings with cancellation cancels along postcomposition of morphisms
of locally adic-star formal algebraic spaces on a size-closed site. -/
theorem etaleAffineLocally.of_comp (h𝒮 : ChosenBigSite.IsSizeClosed 𝒮)
    (hP : IsAdicStarRing.IsLocalMorphismProperty P)
    (hCancel : IsAdicStarRing.HasCancellationProperty P)
    (hgf : etaleAffineLocally P (f ≫ g)) (hg : etaleAffineLocally P g) :
    etaleAffineLocally P f := sorry

/-- Target-cover testing of a local property of continuous homomorphisms of
adic-star rings with cancellation cancels along postcomposition of morphisms
of locally adic-star formal algebraic spaces on a size-closed site. -/
theorem existsCoverOnTarget.of_comp (h𝒮 : ChosenBigSite.IsSizeClosed 𝒮)
    (hP : IsAdicStarRing.IsLocalMorphismProperty P)
    (hCancel : IsAdicStarRing.HasCancellationProperty P)
    (hgf : existsCoverOnTarget P (f ≫ g)) (hg : existsCoverOnTarget P g) :
    existsCoverOnTarget P f := sorry

/-- Source-cover testing of a local property of continuous homomorphisms of
adic-star rings with cancellation cancels along postcomposition of morphisms
of locally adic-star formal algebraic spaces on a size-closed site. -/
theorem existsCoverOnSource.of_comp (h𝒮 : ChosenBigSite.IsSizeClosed 𝒮)
    (hP : IsAdicStarRing.IsLocalMorphismProperty P)
    (hCancel : IsAdicStarRing.HasCancellationProperty P)
    (hgf : existsCoverOnSource P (f ≫ g)) (hg : existsCoverOnSource P g) :
    existsCoverOnSource P f := sorry

end AlgebraicGeometry.IsLocallyAdicStar
