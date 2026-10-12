/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Coextension.BaseChange
import StacksCheckRecall

open CategoryTheory
open scoped TensorProduct Algebra.TensorProduct.Right

universe u

/- 47.14.0.1: for the tensor-product pushout `A' = R' ⊗[R] A` and Tor-independent
`A` and `R'` over `R`, the canonical trivial-duality base-change morphism is
`RHom_R(A, K) ⊗ᴸ_A A' ⟶ RHom_R'(A', K ⊗ᴸ_R R')` in `D(A')`, functorial in
`K : D(R)`. -/
@[stacks 0E29] #check
  (CategoryTheory.ModuleCat.trivialDualityBaseChangeMap :
    ∀ {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
      [Algebra R A] [Algebra R R'] (K : DerivedCategory
        (ModuleCat R))
      (h : CategoryTheory.ModuleCat.Tor.IsIndependent
        (ModuleCat.of R A) (ModuleCat.of R R')),
      (CategoryTheory.ModuleCat.derivedExtensionOfScalars
          (algebraMap A (R' ⊗[R] A))).obj
          ((CategoryTheory.ModuleCat.derivedCoextensionOfScalars
            (algebraMap R A)).obj K) ⟶
        (CategoryTheory.ModuleCat.derivedCoextensionOfScalars
          (algebraMap R' (R' ⊗[R] A))).obj
          ((CategoryTheory.ModuleCat.derivedExtensionOfScalars
            (algebraMap R R')).obj K))
