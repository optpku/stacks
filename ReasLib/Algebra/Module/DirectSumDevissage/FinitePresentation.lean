/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Henselian
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Module.CountablyGenerated.Basic
public import ReasLib.RingTheory.Flatness.MittagLeffler.CountablyGenerated
public import ReasLib.RingTheory.Flatness.MittagLeffler.DirectSum

@[expose] public section

/-!
# Direct sums of finitely presented modules

This leaf owns the proposition-facing internal direct-sum predicate for finitely
presented submodules and its reusable Henselian criterion.  The predicate avoids
the proof-only `DecidableEq` parameter in `DirectSum.IsInternal`; that bundled
form remains available through `iff_internal` as a compatibility view.

The recursive choice of summands is not part of the public API.  Downstream
users should consume the predicate and the two structural criteria below.

@stack 05D6
-/

universe u v w

namespace Module

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- An `R`-module is an internal direct sum of finitely presented submodules.

The index type is deliberately universe-polymorphic and no `DecidableEq` is
stored in the owner predicate. -/
@[stacks 05D6 "internal direct sum of finitely presented submodules"]
def IsDirectSumOfFinitePresentation (R : Type u) (M : Type v)
    [Ring R] [AddCommGroup M] [Module R M] : Prop :=
  ∃ (ι : Type w) (A : ι → Submodule R M),
    iSupIndep A ∧ iSup A = (⊤ : Submodule R M) ∧
      ∀ i, Module.FinitePresentation R (A i)

namespace IsDirectSumOfFinitePresentation

/-- Compatibility view through Mathlib's `DirectSum.IsInternal` packaging.

The explicit `DecidableEq` witness is kept only at this bridge boundary; it
is not required by `Module.IsDirectSumOfFinitePresentation` itself. -/
theorem iff_internal :
    IsDirectSumOfFinitePresentation.{u, v, w} R M ↔
      ∃ (ι : Type w) (_ : DecidableEq ι) (A : ι → Submodule R M),
        DirectSum.IsInternal A ∧ ∀ i, Module.FinitePresentation R (A i) := sorry

/-- Every countably generated module with the complement-summand property is
an internal direct sum of finitely presented submodules. -/
def HasComplementSummand (R : Type u) (M : Type v)
    [Ring R] [AddCommGroup M] [Module R M] : Prop :=
  ∀ ⦃N N' : Submodule R M⦄, IsCompl N N' →
    Module.FinitePresentation R N' →
    ∀ x : N, ∃ F F' : Submodule R N,
      x ∈ F ∧ Module.FinitePresentation R F ∧ IsCompl F F'

/-- Structural countable direct-sum criterion from complemented finite pieces. -/
theorem of_hasComplementSummand
    (hcg : Module.CountablyGenerated R M)
    (hproperty : HasComplementSummand R M) :
    IsDirectSumOfFinitePresentation.{u, v, w} R M := sorry

/-- Over a Henselian local ring, the complement-summand property follows from
the Mittag-Leffler factorization criterion. -/
theorem hasComplementSummand_of_henselian
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    {M : Type v} [AddCommGroup M] [Module R M]
    (hcg : Module.CountablyGenerated R M)
    (hML : Module.MittagLeffler R M) :
    HasComplementSummand R M := sorry

/-- Lemma 10.153.13 (tag `05D6`): a countably generated Mittag-Leffler
module over a Henselian local ring is an internal direct sum of finitely
presented submodules. -/
@[stacks 05D6 "Henselian Mittag-Leffler direct-sum criterion"]
theorem of_henselian
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    {M : Type v} [AddCommGroup M] [Module R M]
    (hcg : Module.CountablyGenerated R M)
    (hML : Module.MittagLeffler R M) :
    IsDirectSumOfFinitePresentation.{u, v, w} R M := sorry

end IsDirectSumOfFinitePresentation

end Module
