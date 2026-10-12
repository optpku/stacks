/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap66.Lemma_66_10_3_LocalRingDim
public import stacks_project.Chap67.Definition_67_15_4_SchemeTheoreticSupport
public import stacks_project.Chap67.Lemma_67_15_1_ModuleSupport
public import stacks_project.Chap71.Lemma_71_2_3_WeaklyAssociated

/-!
# Lemma 71.2.6

A codimension-`0` point of an algebraic space that lies in the support of a
quasi-coherent module is weakly associated to that module. The same holds for a
codimension-`0` point of the scheme-theoretic support of a finite-type module.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- Lemma 71.2.6 (1): for a scheme `S`, an algebraic space `X` over `S`, a
quasi-coherent `𝒪_X`-module `F`, and a point `x` of `Points X`, if `x` lies in
`F.moduleSupport` and `x` is a codimension `0` point of `X` in the sense of
Properties of Spaces, Definition 66.10.2, i.e. `localRingDimAt x = 0`, then
`x ∈ F.weakAss`. -/
@[stacks 0CUL]
theorem mem_weakAss_of_codimZero_moduleSupport (F : X.Modules) [F.IsQuasicoherent]
    {x : Points X} (hx : x ∈ F.moduleSupport) (hdim : localRingDimAt x = 0) :
    x ∈ F.weakAss :=
  sorry

/-- Lemma 71.2.6 (2): for a scheme `S`, an algebraic space `X` over `S`, and a
finite-type quasi-coherent `𝒪_X`-module `F` with scheme-theoretic support
`schemeTheoreticSupport F` in the sense of Morphisms of Spaces,
Definition 67.15.4, if `z` is a codimension `0` point of
`(schemeTheoreticSupport F).X`, i.e. `localRingDimAt z = 0`, then the image
`Points.map (schemeTheoreticSupport F).ι z` lies in `F.weakAss`. -/
@[stacks 0CUL]
theorem mem_weakAss_of_codimZero_schemeTheoreticSupport
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    {z : Points (schemeTheoreticSupport F).X} (hdim : localRingDimAt z = 0) :
    Points.map (schemeTheoreticSupport F).ι z ∈ F.weakAss :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
