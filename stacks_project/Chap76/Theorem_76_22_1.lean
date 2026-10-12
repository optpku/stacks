/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap67.Lemma_67_31_3_FlatOver

/-!
# Openness of the relative flat locus on algebraic spaces

If a morphism of algebraic spaces is locally of finite presentation and a module
sheaf on the source is finitely presented, the locus of points at which the module
is flat over the target is open in the space of points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- The locus of points of `X` at which a quasi-coherent module `F` is flat over `Y`. -/
def flatOverLocus {S : Scheme.{u}} {X Y : AlgebraicSpace S} (F : X.Modules)
    (f : X ⟶ Y) : Set (Points X) :=
  {x | flatOverAt F f x}

/-- Membership in `flatOverLocus F f` is pointwise relative flatness of `F` over `Y`. -/
theorem mem_flatOverLocus {S : Scheme.{u}} {X Y : AlgebraicSpace S} (F : X.Modules)
    (f : X ⟶ Y) (x : Points X) :
    x ∈ flatOverLocus F f ↔ flatOverAt F f x :=
  sorry

/-- Theorem 76.22.1: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S`. Let `F` be a quasi-coherent sheaf on `X`. If `f` is locally of finite
presentation and `F` is an `𝒪_X`-module which is locally of finite presentation, then
`flatOverLocus F f` is open in `|X|`. -/
@[stacks 05WV]
theorem isOpen_flatOverAt {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] (F : X.Modules) [F.IsFinitePresentation] :
    IsOpen (flatOverLocus F f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
