/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Homology

@[expose] public section

open CategoryTheory
open scoped TensorProduct

noncomputable section

universe u

namespace CategoryTheory.ModuleCat

variable
    {R A R' A' : Type u} [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
    [Algebra R A] [Algebra R R'] (σ : (A ⊗[R] R') →+* A')
    (KBase : DerivedCategory (ModuleCat (A ⊗[R] R')))
    (K' : DerivedCategory (ModuleCat A'))
    (α : (derivedExtensionOfScalars σ).obj KBase ⟶ K') (i : ℤ)

#check (cohomologyBaseChangeMap σ KBase K' α i :
    (ModuleCat.extendScalars σ).obj
        ((DerivedCategory.homologyFunctor (ModuleCat (A ⊗[R] R')) i).obj KBase) ⟶
      (DerivedCategory.homologyFunctor (ModuleCat A') i).obj K')

end CategoryTheory.ModuleCat

end
