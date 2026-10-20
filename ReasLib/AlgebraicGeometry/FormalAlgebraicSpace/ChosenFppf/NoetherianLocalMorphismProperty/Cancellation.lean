module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.NoetherianLocalMorphismProperty
public import ReasLib.RingTheory.Topology.Noetherian.Cancellation

/-!
# Cancellation of local properties of locally Noetherian formal algebraic spaces

Cancellation of local properties of continuous maps of Noetherian adic rings
passes to morphisms of locally Noetherian formal algebraic spaces.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ChosenBigFppfSite TopologicalRing

universe u v

namespace AlgebraicGeometry.IsFormalAlgebraicSpace.IsLocallyNoetherian

variable {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
variable [hSheafify : HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
variable [hPullbacks : HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
variable {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
variable [hX : IsLocallyNoetherian X] [hY : IsLocallyNoetherian Y]
    [hZ : IsLocallyNoetherian Z]
variable (P : ∀ {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
    [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B],
    (B →+* A) → Prop)
variable (f : X ⟶ Y) (g : Y ⟶ Z)

include hSheafify hPullbacks hX hY hZ

/-- A local property of continuous maps of Noetherian adic rings with cancellation
cancels along postcomposition when tested on affine étale charts of locally
Noetherian formal algebraic spaces. -/
theorem etaleAffineLocally.of_comp (hP : Noetherian.IsLocalMorphismProperty P)
    (hCancel : Noetherian.HasCancellationProperty P)
    (hgf : etaleAffineLocally P (f ≫ g)) (hg : etaleAffineLocally P g) :
    etaleAffineLocally P f := sorry

/-- A local property of continuous maps of Noetherian adic rings with cancellation
cancels along postcomposition in the target-cover formulation for locally
Noetherian formal algebraic spaces. -/
theorem existsCoverOnTarget.of_comp (hP : Noetherian.IsLocalMorphismProperty P)
    (hCancel : Noetherian.HasCancellationProperty P)
    (hgf : existsCoverOnTarget P (f ≫ g)) (hg : existsCoverOnTarget P g) :
    existsCoverOnTarget P f := sorry

/-- A local property of continuous maps of Noetherian adic rings with cancellation
cancels along postcomposition in the source-cover formulation for locally
Noetherian formal algebraic spaces. -/
theorem existsCoverOnSource.of_comp (hP : Noetherian.IsLocalMorphismProperty P)
    (hCancel : Noetherian.HasCancellationProperty P)
    (hgf : existsCoverOnSource P (f ≫ g)) (hg : existsCoverOnSource P g) :
    existsCoverOnSource P f := sorry

end AlgebraicGeometry.IsFormalAlgebraicSpace.IsLocallyNoetherian
