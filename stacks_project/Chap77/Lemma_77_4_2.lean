module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Definition_66_29_1_RingedSite
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_31_3_FlatOver
public import stacks_project.Chap68.Lemma_68_18_10_Fibre

/-!
# Openness of the relative flat locus in a set-theoretic fibre

For a locally finite-type morphism of algebraic spaces and a finite-type
quasi-coherent module on the source, the locus of points of a set-theoretic
fibre at which the module is flat over the target is open in that fibre.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- The locus in the set-theoretic fibre `fiberOver f y` at which `ℱ` is
flat over `Y`. -/
def fiberFlatOverLocus {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (ℱ : X.Modules) (f : X ⟶ Y) (y : Points Y) : Set (fiberOver f y) :=
  {x | flatOverAt ℱ f x.val}

/-- Membership in `fiberFlatOverLocus ℱ f y` is pointwise relative flatness of
`ℱ` over `Y` at the underlying point of `X`. -/
theorem mem_fiberFlatOverLocus {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (ℱ : X.Modules) (f : X ⟶ Y) (y : Points Y) (x : fiberOver f y) :
    x ∈ fiberFlatOverLocus ℱ f y ↔ flatOverAt ℱ f x.val :=
  sorry

/-- Lemma 77.4.2: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S` which is locally of finite type. Let `ℱ` be a
quasi-coherent `𝒪_X`-module of finite type. Let `y : Points Y` and write
`F` for the set-theoretic fibre `fiberOver f y ⊂ Points X`. Then the set of
points of `F` at which `ℱ` is flat over `Y` is open in `F`. -/
@[stacks 0CWK]
theorem isOpen_flatOverAt_fiber {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] (ℱ : X.Modules)
    [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (y : Points Y) :
    IsOpen (fiberFlatOverLocus ℱ f y) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
