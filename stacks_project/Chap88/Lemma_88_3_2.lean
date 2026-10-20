/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.AdicCompletion.NaiveCotangent.Completion

/-!
# Lemma 88.3.2

The completed naive cotangent complex of the `I`-adic completion of a finite-type
algebra is identified with the tensor of a chosen polynomial presentation, both
as complexes and after derived extension of scalars.
-/

@[expose] public section

noncomputable section

universe u

open Algebra.NaiveCotangent.Adic
open Algebra.Extension.NaiveCotangent.BaseChange
open CategoryTheory

namespace Algebra.NaiveCotangent.Adic

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
variable {B : Type u} [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
variable {ι : Type u} [Fintype ι]
variable (I : Ideal A)
variable (α : MvPolynomial ι A →ₐ[A] B) (hα : Function.Surjective α)

/- Lemma 88.3.2 (1): The completed naive cotangent complex is the tensor base
change of the complex of the chosen finite polynomial presentation. -/
@[stacks 0GAF] #check (Algebra.NaiveCotangent.Adic.tensorIso I α hα :
  naiveCotangent I (completionPresentation I α hα) ≅
    Algebra.Extension.NaiveCotangent.BaseChange.tensorModel (polynomialExtension α hα))

/- Lemma 88.3.2 (2): The completed naive cotangent object is the derived base
change of the ordinary naive cotangent object. -/
@[stacks 0GAF] #check (Algebra.NaiveCotangent.Adic.derivedTensorIso I α hα :
  naiveCotangentObject I (completionPresentation I α hα) ≅
    (ModuleCat.derivedExtensionOfScalars
        (algebraMap B (algebraCompletion I B))).obj
      (Algebra.naiveCotangentObject A B))

end Algebra.NaiveCotangent.Adic
