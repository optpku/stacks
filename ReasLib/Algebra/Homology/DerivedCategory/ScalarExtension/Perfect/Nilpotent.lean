/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Perfect
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.TorAmplitude
public import Mathlib.RingTheory.FinitePresentation
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Relative perfectness across a nilpotent base change

@stack 0DJG

This leaf owns the nilpotent-thickening converse to
`DerivedCategory.IsPerfectOver.tensorBaseChange`.  The scalar-extension object is formed by the
explicit left inclusion `A' → A' ⊗[R'] R`; the right tensor-factor algebra structure supplies the
base ring `R`.  Pseudo-coherence reflection and Tor-amplitude reflection remain independently
available from their property owners.
-/

noncomputable section

open CategoryTheory
open scoped TensorProduct Algebra.TensorProduct.Right

universe u

namespace CategoryTheory.DerivedCategory.IsPerfectOver.Nilpotent

variable {R' A' R : Type u} [CommRing R'] [CommRing A'] [CommRing R]
variable [Algebra R' A'] [Algebra R' R]
variable [Module.Flat R' A'] [Algebra.FinitePresentation R' A']

/-- The canonical derived tensor base change of an `A'`-complex from `R'` to `R`, written with
the explicit left tensor-factor homomorphism. -/
@[stacks 0DJG "derived tensor base change along the left factor"]
noncomputable abbrev tensorBaseChange (K : DerivedCategory (ModuleCat A')) :
    DerivedCategory (ModuleCat (A' ⊗[R'] R)) :=
  (ModuleCat.derivedExtensionOfScalars
    (Algebra.TensorProduct.includeLeftRingHom : A' →+* A' ⊗[R'] R)).obj K

/-- Lemma 15.84.8 (Stacks `0DJG`): if `R' → R` is surjective with nilpotent kernel and the
derived tensor base change of `K` is perfect relative to `R`, then `K` is perfect relative to
`R'`. -/
@[stacks 0DJG "relative perfectness descends across a nilpotent base change"]
theorem of_tensorBaseChange
    (hσ : Function.Surjective (algebraMap R' R))
    (hker : IsNilpotent (RingHom.ker (algebraMap R' R)))
    {K : DerivedCategory (ModuleCat A')}
    (hK : IsPerfectOver (A := A' ⊗[R'] R) R (tensorBaseChange (R := R) K)) :
    IsPerfectOver R' K := sorry
/- Proof strategy: split `hK` with `isPerfectOver_iff`; reflect pseudo-coherence through
`DerivedCategory.IsPseudoCoherent.extension_iff`, and reflect finite Tor dimension with
`HasFiniteTorDimension.extension_iff_of_surjective_of_nilpotent_ker`, using the explicit
left-factor tensor base-change object in both comparisons. -/

/-- Relative perfectness is equivalent before and after a surjective nilpotent tensor base
change.  The forward implication is the ordinary flat base-change theorem; the reverse implication
is `of_tensorBaseChange`. -/
@[stacks 0DJG "relative perfectness across a nilpotent base change"]
theorem tensorBaseChange_iff
    (hσ : Function.Surjective (algebraMap R' R))
    (hker : IsNilpotent (RingHom.ker (algebraMap R' R)))
    (K : DerivedCategory (ModuleCat A')) :
    IsPerfectOver (A := A' ⊗[R'] R) R (tensorBaseChange (R := R) K) ↔
      IsPerfectOver R' K := sorry
/- Proof strategy: the forward implication is `of_tensorBaseChange`; for the reverse implication,
identify `tensorBaseChange` with the tensor-product scalar extension and apply
`IsPerfectOver.tensorBaseChange`. -/

end CategoryTheory.DerivedCategory.IsPerfectOver.Nilpotent

end
