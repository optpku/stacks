module

public import Mathlib.Topology.Sets.Closeds
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.StrictTransform.Comparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.IsomorphismLocus
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Support

/-!
# Proper morphisms and admissible blowups of algebraic spaces

A proper morphism of quasi-compact, quasi-separated algebraic spaces that is an
isomorphism near a closed subset of a quasi-compact open admits an admissible
blowup whose strict transform is an isomorphism near the closure of that subset.
A proper morphism to a quasi-compact, quasi-separated algebraic space that is an
isomorphism over a quasi-compact open admits an admissible blowup whose strict
transform is globally an isomorphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A proper morphism of quasi-compact, quasi-separated algebraic spaces that is
an isomorphism near a closed subset of a quasi-compact open has, after an
admissible blowup, a strict transform that is an isomorphism near the closure of
the lifted subset. -/
theorem exists_isAdmissibleBlowup_strictTransform_isIso_near_closure
    {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    (f : X ⟶ Y) [Proper f]
    (V : OpenSubspace Y) [QuasiCompact V.ι]
    (T : TopologicalSpace.Closeds (Points V.X))
    (hT : (T : Set (Points V.X)) ⊆
      isomorphismLocus (restrictTo f V)) :
    ∃ (Y' : AlgebraicSpace S) (b : Y' ⟶ Y) (Z : ClosedSubspace Y)
      (h_blowup : IsBlowup b Z) (h_fp : FinitePresentation Z.ι)
      (h_disjoint : Disjoint Z.pointsSet V.pointsSet)
      (h_quasiCompact :
        QuasiCompact (strictTransformOpenComplement b (Z.inverseImageSubspace b) f).ι),
      closure (Points.map b ⁻¹' (Points.map V.ι '' (T : Set (Points V.X)))) ⊆
        isomorphismLocus (strictTransformSnd b (Z.inverseImageSubspace b) f) :=
  sorry

/-- A proper morphism to a quasi-compact, quasi-separated algebraic space that is
an isomorphism over a quasi-compact open has an isomorphic strict transform after
a blowup in a finitely presented closed center disjoint from that open. -/
theorem exists_isAdmissibleBlowup_strictTransform_isIso
    {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [IsQuasiCompact B] [IsAbsolutelyQuasiSeparated B]
    (f : X ⟶ B) [Proper f]
    (U : OpenSubspace B) [IsQuasiCompact U.X]
    [IsIso (pullback.snd f U.ι)] :
    ∃ (B' : AlgebraicSpace S) (b : B' ⟶ B) (Z : ClosedSubspace B)
      (h_quasiCompact :
        QuasiCompact (strictTransformOpenComplement b (Z.inverseImageSubspace b) f).ι),
      IsBlowup b Z ∧ FinitePresentation Z.ι ∧ Disjoint Z.pointsSet U.pointsSet ∧
        IsIso (strictTransformSnd b (Z.inverseImageSubspace b) f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
