/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.LocalMorphismProperty
public import ReasLib.RingTheory.Topology.WeaklyAdmissible.Cancellation

/-!
# Cancellation of local properties of locally countably indexed formal algebraic spaces

Cancellation of local properties of continuous maps of countably indexed weakly
admissible rings passes to morphisms of locally countably indexed formal algebraic
spaces.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ChosenBigFppfSite TopologicalRing

universe u v

namespace AlgebraicGeometry.IsLocallyCountablyIndexed

variable {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
variable [hSheafify : HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
variable [hPullbacks : HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
variable {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
variable [hX : IsLocallyCountablyIndexed X] [hY : IsLocallyCountablyIndexed Y]
    [hZ : IsLocallyCountablyIndexed Z]
variable (P : ∀ {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
    [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B],
    (B →+* A) → Prop)
variable (f : X ⟶ Y) (g : Y ⟶ Z)

include hSheafify hPullbacks hX hY hZ

/-- A local property of continuous maps of countably indexed weakly admissible
rings with cancellation cancels along postcomposition when tested on affine étale charts
of locally countably indexed formal algebraic spaces. -/
theorem etaleAffineLocally.of_comp (hP : IsLocalMorphismProperty P)
    (hCancel : HasCancellationProperty P)
    (hgf : etaleAffineLocally P (f ≫ g)) (hg : etaleAffineLocally P g) :
    etaleAffineLocally P f := sorry

/-- A local property of continuous maps of countably indexed weakly admissible
rings with cancellation cancels along postcomposition in the target-cover formulation
of locally countably indexed formal algebraic spaces. -/
theorem existsCoverOnTarget.of_comp (hP : IsLocalMorphismProperty P)
    (hCancel : HasCancellationProperty P)
    (hgf : existsCoverOnTarget P (f ≫ g)) (hg : existsCoverOnTarget P g) :
    existsCoverOnTarget P f := sorry

/-- A local property of continuous maps of countably indexed weakly admissible
rings with cancellation cancels along postcomposition in the source-cover formulation
of locally countably indexed formal algebraic spaces. -/
theorem existsCoverOnSource.of_comp (hP : IsLocalMorphismProperty P)
    (hCancel : HasCancellationProperty P)
    (hgf : existsCoverOnSource P (f ≫ g)) (hg : existsCoverOnSource P g) :
    existsCoverOnSource P f := sorry

end AlgebraicGeometry.IsLocallyCountablyIndexed
