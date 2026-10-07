module

public import stacks_project.Chap92.«92_15_0_1_TensorProduct»
public import ReasLib.Algebra.Category.ModuleCat.Tor.Independence
import Mathlib.Tactic.CrossRefAttribute

/-!
# Tensor-product cotangent complex of Tor-independent algebras

If `A` and `B` are Tor-independent `R`-algebras, the tensor-product cone `E` of
(92.15.0.1) vanishes in `D(Mod (A ⊗[R] B))`, and `sumMap` is an isomorphism.
-/

@[expose] public section

open Algebra.CotangentComplex
open CategoryTheory
open CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace Algebra.CotangentComplex

/-- Lemma 92.15.1 (1): if `A` and `B` are Tor-independent `R`-algebras, then the
object `E` in (92.15.0.1) is zero in `D(Mod (A ⊗[R] B))`. -/
@[stacks 09DA]
theorem tensorProductCone_isZero_of_torIndependent (R A B : Type u)
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra B (A ⊗[R] B)]
    [IsScalarTower R A (A ⊗[R] B)] [IsScalarTower R B (A ⊗[R] B)]
    (h_torIndependent :
      ModuleCat.Tor.IsIndependent (ModuleCat.of R A) (ModuleCat.of R B)) :
    IsZero (tensorProductCone R A B) :=
  sorry

/-- Lemma 92.15.1 (2): if `A` and `B` are Tor-independent `R`-algebras, then
`L_{A ⊗[R] B / R}` is isomorphic in `D(Mod (A ⊗[R] B))` to the derived biproduct
`L_{A/R} ⊗_A^L (A ⊗[R] B) ⊕ L_{B/R} ⊗_B^L (A ⊗[R] B)`, as invertibility of
`sumMap R A B`. This isomorphism is represented by the cochain biproduct
`tensorProductExtendLeft R A B ⊞ tensorProductExtendRight R A B` of
`A ⊗[R] B`-modules, i.e. the informal complex `L_{A/R} ⊗[R] B ⊕ L_{B/R} ⊗[R] A`. -/
@[stacks 09DA]
theorem sumMap_isIso_of_torIndependent (R A B : Type u)
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra B (A ⊗[R] B)]
    [IsScalarTower R A (A ⊗[R] B)] [IsScalarTower R B (A ⊗[R] B)]
    (h_torIndependent :
      ModuleCat.Tor.IsIndependent (ModuleCat.of R A) (ModuleCat.of R B)) :
    IsIso (sumMap R A B) :=
  sorry

/-- Object-level form of invertibility of `sumMap`: `derived R (A ⊗[R] B)` is
isomorphic to `DerivedCategory.Q.obj` of the cochain biproduct
`tensorProductExtendLeft R A B ⊞ tensorProductExtendRight R A B`. -/
theorem isIsomorphic_derived_sumMapSource_of_torIndependent (R A B : Type u)
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra B (A ⊗[R] B)]
    [IsScalarTower R A (A ⊗[R] B)] [IsScalarTower R B (A ⊗[R] B)]
    (h_torIndependent :
      ModuleCat.Tor.IsIndependent (ModuleCat.of R A) (ModuleCat.of R B)) :
    IsIsomorphic (derived R (A ⊗[R] B))
      (DerivedCategory.Q.obj
        (tensorProductExtendLeft R A B ⊞ tensorProductExtendRight R A B)) :=
  sorry

end Algebra.CotangentComplex
