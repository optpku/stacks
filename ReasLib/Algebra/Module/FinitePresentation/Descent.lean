/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Finiteness.Descent
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Faithfully flat descent of finite presentation

Mathlib already descends finite generation of modules and finite presentation of algebras.
This leaf supplies the corresponding module finite-presentation theorem, with both module-class
and explicit ring-hom interfaces.
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Module.FinitePresentation

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module R M]

/-- Finite presentation descends from `S ⊗[R] M` along a faithfully flat scalar extension. -/
@[stacks 03C4 "faithfully flat descent of module finite presentation"]
theorem of_tensorProduct_of_faithfullyFlat
    [Module.FaithfullyFlat R S]
    [Module.FinitePresentation S (S ⊗[R] M)] :
    Module.FinitePresentation R M := sorry

/-- Compatibility entry for the former long theorem name.  New code should use
`Module.FinitePresentation.of_tensorProduct_of_faithfullyFlat`. -/
theorem of_finitePresentation_tensorProduct_of_faithfullyFlat
    [Module.FaithfullyFlat R S]
    [Module.FinitePresentation S (S ⊗[R] M)] :
    Module.FinitePresentation R M := sorry

attribute [deprecated Module.FinitePresentation.of_tensorProduct_of_faithfullyFlat
    (since := "2026-08-07")]
  of_finitePresentation_tensorProduct_of_faithfullyFlat

end Module.FinitePresentation

namespace RingHom.FaithfullyFlat

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module R M]

/-- An explicit faithfully flat algebra map descends finite presentation from the tensor
base change, without requiring callers to install a temporary module instance. -/
@[stacks 03C4 "explicit faithfully flat map descent of module finite presentation"]
theorem moduleFinitePresentation_of_tensorProduct
    (hff : (algebraMap R S).FaithfullyFlat)
    [Module.FinitePresentation S (S ⊗[R] M)] :
    Module.FinitePresentation R M := sorry

end RingHom.FaithfullyFlat
