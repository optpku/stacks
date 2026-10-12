/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Sets.Closeds
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap71.Lemma_71_18_7_Blowup
public import stacks_project.Chap71.Lemma_71_18_7_Comparison
public import stacks_project.Chap72.Lemma_72_3_3_IsomorphismLocus

/-!
# Isomorphisms near a closed subset after admissible blowups

A proper morphism of qcqs algebraic spaces that is an isomorphism near a
closed subset of a quasi-compact open has, after a `V`-admissible blowup, a
strict transform that is an isomorphism near the closure of that subset.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 81.14.3. Let `S` be a scheme. Let `f : X ⟶ Y` be a proper morphism of
quasi-compact and quasi-separated algebraic spaces over `S`. Let `V ⊂ Y` be a
quasi-compact open and `U = f⁻¹(V)`. Let `T ⊂ |V|` be a closed subset such that
`f|_U : U ⟶ V` is an isomorphism over an open neighbourhood of `T` in `V`. Then
there exists a `V`-admissible blowing up `Y' ⟶ Y` such that the strict transform
`f' : X' ⟶ Y'` of `f` is an isomorphism over an open neighbourhood of the
closure of `T` in `|Y'|`. -/
@[stacks 0F47]
theorem exists_isAdmissibleBlowup_strictTransform_isIso_near_closure
    {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    (f : X ⟶ Y) [Proper f]
    (V : OpenSubspace Y) [QuasiCompact V.ι]
    (T : TopologicalSpace.Closeds (Points V.X))
    (hT : (T : Set (Points V.X)) ⊆
      isomorphismLocus (openInverseImageTo f V.ι)) :
    ∃ (Y' : AlgebraicSpace S) (b : Y' ⟶ Y) (Z : ClosedSubspace Y)
      (h_blowup : IsBlowup b Z) (h_fp : FinitePresentation Z.ι)
      (h_disjoint : Disjoint Z.pointsSet V.pointsSet)
      (h_quasiCompact :
        QuasiCompact (strictTransformOpenComplement b (Z.inverseImage b) f).ι),
      closure (Points.map b ⁻¹' (Points.map V.ι '' (T : Set (Points V.X)))) ⊆
        isomorphismLocus (strictTransformSnd b (Z.inverseImage b) f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
