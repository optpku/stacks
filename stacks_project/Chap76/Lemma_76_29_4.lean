/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Lemma_66_8_1_Constructible
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap76.Lemma_76_29_3_ReducedFiberLocus

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 76.29.4: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic spaces
over `S` which is quasi-compact and locally of finite presentation. Then the set
`E = geometricallyReducedFiberLocus f` of points of `|Y|` at which the fibre of `f` is
geometrically reduced is étale locally constructible. -/
@[stacks 0E0A]
theorem isEtaleLocallyConstructible_geometricallyReducedFiberLocus
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [LocallyOfFinitePresentation f] :
    IsEtaleLocallyConstructible (geometricallyReducedFiberLocus f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
