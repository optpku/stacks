/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import ReasLib.Algebra.Module.Eilenberg
public import ReasLib.Algebra.Module.StableFree
public import ReasLib.Algebra.Module.CountablyGenerated.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Projective modules of infinite local rank

This leaf owns the finite-summand and freeness results for projective modules whose localizations
at maximal ideals are not finite.  For projective modules those localizations are free, so this is
the source condition that they have infinite rank.

@stack 0GVH
@stack 0GVI
@stack 0GVJ
@stack 0GVK
-/

@[expose] public section

universe u v

namespace Module

/-- A module has infinite rank at every maximal ideal when none of its maximal localizations is
finite.  For projective modules the localized modules are free, so this is the usual infinite-rank
condition. -/
@[stacks 0GVI, stacks 0GVJ, stacks 0GVK "infinite rank at every maximal ideal"]
def HasInfiniteRankAtMaximal
    (R : Type u) (P : Type v) [CommRing R] [AddCommGroup P] [Module R P] : Prop :=
  ∀ m : MaximalSpectrum R,
    ¬ Module.Finite (Localization.AtPrime m.asIdeal) (LocalizedModule.AtPrime m.asIdeal P)

/-- The pointwise characterization of `Module.HasInfiniteRankAtMaximal`. -/
theorem hasInfiniteRankAtMaximal_iff
    {R : Type u} {P : Type v} [CommRing R] [AddCommGroup P] [Module R P] :
    HasInfiniteRankAtMaximal R P ↔
      ∀ m : MaximalSpectrum R,
        ¬ Module.Finite (Localization.AtPrime m.asIdeal)
          (LocalizedModule.AtPrime m.asIdeal P) := sorry
-- Proof strategy: unfold `HasInfiniteRankAtMaximal`; both sides are definitionally identical.

namespace Projective

/-- Lemma 15.129.3: a projective module has a finite free direct summand in a finite-free
stabilization which contains the prescribed element. -/
@[stacks 0GVH]
theorem existsFiniteFreeProdSummandContaining
    {R : Type u} [Ring R] {P : Type v} [AddCommGroup P] [Module R P]
    [Module.Projective R P] (s : P) :
    ∃ (F : Type (max u v)) (_ : AddCommGroup F) (_ : Module R F) (_ : Module.Free R F)
      (_ : Module.Finite R F),
      ∃ K : Complementeds (Submodule R (F × P)),
        Module.Free R (K : Submodule R (F × P)) ∧
          Module.Finite R (K : Submodule R (F × P)) ∧
            ((0 : F), s) ∈ (K : Submodule R (F × P)) := sorry
-- Proof strategy: use projectivity to obtain a dual-basis presentation of `P`, retain the finite
-- fragment that supports `s`, and stabilize that finite projective fragment by a finite free
-- module.  Its image in `F × P` is complemented, finite free, and contains `(0, s)`.

/-- Lemma 15.129.4: after perturbing a generator modulo a submodule, its cyclic span can be made
a free direct summand. -/
@[stacks 0GVI]
theorem existsCyclicFreeSummandOfPerturbation
    {R : Type u} [CommRing R] {P : Type v} [AddCommGroup P] [Module R P]
    [Module.Projective R P] [IsNoetherianRing (R ⧸ Ring.jacobson R)]
    (M : Submodule R P) (s : P) (hP : HasInfiniteRankAtMaximal R P)
    (hspan : R ∙ s + M = ⊤) :
    ∃ m : M, IsComplemented (R ∙ (s + m)) ∧ Module.Free R (R ∙ (s + m)) := sorry
-- Proof strategy: work modulo the Jacobson radical and use Noetherian prime avoidance to choose
-- `m : M` outside the finitely many bad loci where `s + m` fails to be unimodular.  Infinite local
-- rank supplies an unused coordinate at every maximal localization, so the cyclic span is free
-- and locally, hence globally, complemented.

/-- Lemma 15.129.5: every element lies in a finite stably free direct summand when the projective
module has infinite rank at every maximal ideal. -/
@[stacks 0GVJ]
theorem existsFiniteStablyFreeSummandContaining
    {R : Type u} [CommRing R] {P : Type v} [AddCommGroup P] [Module R P]
    [Module.Projective R P] [IsNoetherianRing (R ⧸ Ring.jacobson R)]
    (s : P) (hP : HasInfiniteRankAtMaximal R P) :
    ∃ M : Submodule R P,
      s ∈ M ∧ IsComplemented M ∧ Module.Finite R M ∧ Module.StablyFree R M := sorry
-- Proof strategy: start with the finite free complemented summand containing `(0, s)` in a finite
-- stabilization, then use the perturbation lemma to split off the stabilization coordinates one
-- at a time.  Transport the remaining finite complemented summand back to `P`; the discarded
-- finite free factors give its stable-freeness witness.

/-- Theorem 15.129.6: a countably generated projective module of infinite rank at every maximal
ideal is free when the quotient by the Jacobson radical is Noetherian. -/
@[stacks 0GVK]
theorem freeOfCountablyGeneratedOfInfiniteRankAtMaximal
    {R : Type u} [CommRing R] {P : Type v} [AddCommGroup P] [Module R P]
    [Module.Projective R P] [IsNoetherianRing (R ⧸ Ring.jacobson R)]
    (hcg : Module.CountablyGenerated R P) (hP : HasInfiniteRankAtMaximal R P) :
    Module.Free R P := sorry
-- Proof strategy: enumerate a countable generating family and recursively enlarge finite
-- stably-free complemented summands so the `n`th stage contains the `n`th generator.  Choose free
-- complements compatibly using Eilenberg absorption; the increasing union of their finite bases is
-- a basis of `P`.

end Projective

end Module
