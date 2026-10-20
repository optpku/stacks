module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.Locus
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap67.Lemma_67_31_3_FlatOver
import StacksCheckRecall

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

/- Theorem 76.22.1: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S`. Let `F` be a quasi-coherent sheaf on `X`. If `f` is locally of finite
presentation and `F` is an `𝒪_X`-module which is locally of finite presentation, then
`flatOverLocus F f` is open in `|X|`. -/
@[stacks 05WV] #check (AlgebraicGeometry.AlgebraicSpace.Modules.isOpen_flatOverAt :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [AlgebraicGeometry.AlgebraicSpace.LocallyOfFinitePresentation f]
    (F : X.Modules) [F.IsFinitePresentation],
    IsOpen (AlgebraicGeometry.AlgebraicSpace.Modules.flatOverLocus F f))

end AlgebraicGeometry.AlgebraicSpace.Modules
