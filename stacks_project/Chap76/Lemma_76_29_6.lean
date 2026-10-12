/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap76.Lemma_76_29_3_ReducedFiberLocus

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 76.29.6: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S`. If `f` is flat, proper, and of finite presentation, then the set
`E = geometricallyReducedFiberLocus f` of points of `|Y|` at which the fibre of `f`
is geometrically reduced is open in `|Y|`. -/
@[stacks 0E0C]
theorem isOpen_geometricallyReducedFiberLocus {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Flat f] [Proper f] [FinitePresentation f] :
    IsOpen (geometricallyReducedFiberLocus f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
