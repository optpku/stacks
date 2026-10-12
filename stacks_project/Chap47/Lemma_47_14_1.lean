/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Coextension.BaseChange.InternalHom

@[expose] public section

noncomputable section

open CategoryTheory
open DerivedCategory
open DerivedTensor.Right.Monoidal
open InternalHom.TensorLeft

universe u

/- Lemma 47.14.1: In the tensor-product pushout situation, the trivial-duality
base-change map is an isomorphism if and only if the canonical map
`RHom_R(A, K) ⊗ᴸ_R R' ⟶ RHom_R(A, K ⊗ᴸ_R R')` is an isomorphism. -/
@[stacks 0E2A] #check
  (CategoryTheory.ModuleCat.trivialDualityBaseChangeMap_isIso_iff_tensorLeftComparison :
    ∀ {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
      [Algebra R A] [Algebra R R']
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} R))]
      [BraidedCategory (DerivedCategory (ModuleCat.{u} R))]
      (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} R)))
      (T : Model)
      (K : DerivedCategory (ModuleCat.{u} R))
      (h : CategoryTheory.ModuleCat.Tor.IsIndependent
        (ModuleCat.of R A) (ModuleCat.of R R')),
      IsIso (CategoryTheory.ModuleCat.trivialDualityBaseChangeMap K h) ↔
        IsIso (comparisonOf H T
          (ModuleCat.single0 (ModuleCat.of R R')) K
          (ModuleCat.single0 (ModuleCat.of R A))))
