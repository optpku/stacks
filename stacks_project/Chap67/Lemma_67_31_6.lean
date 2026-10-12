/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_6_3_UniversallyOpen
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap67.Lemma_67_31_3_FlatOver
public import stacks_project.Chap67.Lemma_67_31_6_ModuleSupport

/-!
# Universal openness from a relatively flat finite-type module of full support

A morphism of algebraic spaces that is locally of finite presentation, and that carries a
quasi-coherent finite-type module of full support which is flat over the target, is
universally open.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Lemma 67.31.6: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic spaces
over `S`. Let `F` be a quasi-coherent `𝒪_X`-module. If `f` is locally of finite presentation,
`F` is of finite type, `moduleSupport F = Set.univ`, and `F` is flat over `Y`, then `f` is
universally open. -/
@[stacks 0CVU]
theorem universallyOpen_of_flatOver_of_moduleSupport_eq_univ
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] [LocallyOfFinitePresentation f]
    (hsupp : moduleSupport F = Set.univ) (hflat : flatOver F f) :
    UniversallyOpen f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
