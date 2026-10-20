module

public import stacks_project.Chap65.Definition_65_12_1_Subspace
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap67.Definition_67_14_4_Subscheme
public import stacks_project.Chap67.Lemma_67_28_12_IdealSheaf

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Ideal
import StacksCheckRecall

/-! # Closed subspaces and quasi-coherent ideals

The public ideal owner carries the original actual vanishing subfunctor,
inclusion, intersections/unions, and closed-subspace correspondence.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check
  (AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.idealSheaf :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (Z : ClosedSubspace X), IdealSubobject X)

#check
  (AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.idealSheaf_eq :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (Z : ClosedSubspace X),
      Z.idealSheaf = Hom.idealSheafSubobject Z.ι)

/- Lemma 67.13.1. Every quasi-coherent ideal sheaf defines a closed subspace
through its vanishing subfunctor. -/
@[stacks 03MB] #check
  (AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.ofQuasiCoherentIdeal :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (I : IdealSubobject X) [IsQuasiCoherent I],
      ClosedSubspace X)

#check
  (AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.ofQuasiCoherentIdeal_ι :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (I : IdealSubobject X) [IsQuasiCoherent I],
      (ClosedSubspace.ofQuasiCoherentIdeal I).ι = subschemeι I)

