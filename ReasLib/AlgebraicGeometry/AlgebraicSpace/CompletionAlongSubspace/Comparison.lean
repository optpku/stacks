/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlongSubspace
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation

/-!
# Comparison of completions along a closed immersion

Completion along a closed immersion maps to completion along its closed support
by the identity on underlying sections. This comparison is an isomorphism when
the closed immersion is of finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace ClosedSubspace

/-- The closed set of points of the ambient space underlying a closed subspace. -/
def pointsCloseds {S : Scheme.{u}} {X : AlgebraicSpace S} (Z : ClosedSubspace X) :
    Closeds (Points X) where
  carrier := Z.pointsSet
  isClosed' := isClosed_pointsSet Z

/-- The carrier of the closed support is the underlying point set of the subspace. -/
theorem pointsCloseds_carrier {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Z : ClosedSubspace X) :
    (Z.pointsCloseds : Set (Points X)) = Z.pointsSet :=
  rfl

/-- A point belongs to the closed support exactly when it belongs to the subspace's point set. -/
theorem mem_pointsCloseds {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Z : ClosedSubspace X) {x : Points X} :
    x ∈ Z.pointsCloseds ↔ x ∈ Z.pointsSet :=
  Iff.rfl

end ClosedSubspace

/-- A section that fppf-locally factors through an infinitesimal neighbourhood
of a closed immersion has image contained in its closed support. -/
theorem mapsInto_of_fppfLocallyFactorsThroughNeighbourhood
    {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i]
    {U : (Over S)ᵒᵖ} {x : X.functorOfPoints.obj U}
    (hx : fppfLocallyFactorsThroughNeighbourhood i x) :
    mapsInto ((ClosedSubspace.ofι i).pointsCloseds : Set (Points X)) x :=
  sorry

namespace completionAlongSubspace

/-- The canonical comparison from completion along a closed immersion to
completion along its closed support, acting identically on underlying sections. -/
def toCompletionAlong {S : Scheme.{u}} {X Z : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i] :
    completionAlongSubspace i ⟶ completionAlong X (ClosedSubspace.ofι i).pointsCloseds where
  app _ :=
    ofHom fun x ↦
      ⟨x.1, mapsInto_of_fppfLocallyFactorsThroughNeighbourhood i x.2⟩
  naturality := sorry

/-- The comparison commutes with the canonical inclusions into the ambient functor of points. -/
theorem toCompletionAlong_comp_ι {S : Scheme.{u}} {X Z : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i] :
    toCompletionAlong i ≫ completionAlong.ι X (ClosedSubspace.ofι i).pointsCloseds = ι i :=
  sorry

/-- The comparison leaves the underlying section of the ambient space unchanged. -/
theorem toCompletionAlong_app {S : Scheme.{u}} {X Z : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i] (U : (Over S)ᵒᵖ)
    (x : (completionAlongSubspace i).obj U) :
    (completionAlong.ι X (ClosedSubspace.ofι i).pointsCloseds).app U
        ((toCompletionAlong i).app U x) =
      (ι i).app U x :=
  sorry

end completionAlongSubspace

/-- Completion along a finite-presentation closed immersion agrees with
completion along its closed support. -/
instance isIso_toCompletionAlong {S : Scheme.{u}} {X Z : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i] [FinitePresentation i] :
    IsIso (completionAlongSubspace.toCompletionAlong i) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
