module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FlatAlgebra
public import ReasLib.RingTheory.Henselian.Pair.Basic
public import ReasLib.RingTheory.Henselian.Pair.Category
public import stacks_project.Chap93.Example_93_8_1_Rings_Category

public import ReasLib.AlgebraicGeometry.FormalDeformation.FlatAlgebra.Henselization
import StacksCheckRecall

/-!
# Henselization of ring deformation categories

Canonical pair henselization induces a functor on flat deformations.
-/

@[expose] public section

open CategoryTheory RingPairCat

universe u

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (P : Type u) [CommRing P] [Algebra k P] (J : Ideal P)

/- Lemma 93.8.8 (Henselization)
Henselization of a ring pair induces the corresponding functor on deformation categories.
-/
@[stacks 0DYT] #check (FlatAlgebraCat.henselizationFunctor Λ k P J :
  FlatAlgebraCat.deformationCategory Λ k P ⥤
    FlatAlgebraCat.deformationCategory Λ k (henselizationRing (pairOfIdeal J) : Type u))

#check (FlatAlgebraCat.henselizationFunctor_obj_algebra Λ k P J :
  ∀ (x : FlatAlgebraCat.deformationCategory Λ k P),
    ((FlatAlgebraCat.henselizationFunctor Λ k P J).obj x).left.algebra =
      FlatAlgebraCat.objHenselizationRing Λ k P J x)
