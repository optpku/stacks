/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.PureProjective.Presentation
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped DirectSum

universe u

variable {R : Type u} [CommRing R]

/- Lemma 46.8.2 (1): an `R`-module is pure projective if and only if it is a direct
summand of a direct sum of finitely presented `R`-modules. -/
@[stacks 06ZZ]
#check
  (ModuleCat.PureProjective.iff_retract_directSum_finitePresentation :
    ∀ M : ModuleCat.{u} R,
      M.PureProjective ↔
        ∃ (ι : Type u) (P : ι → ModuleCat.{u} R),
          (∀ i, Module.FinitePresentation R (P i)) ∧
            Nonempty (CategoryTheory.Retract M (ModuleCat.of R (⨁ i, P i))))

/- Lemma 46.8.2 (2): every `R`-module is the last term of a universally exact short
complex whose middle term is pure projective. -/
@[stacks 06ZZ]
#check
  (ModuleCat.exists_universallyExact_pureProjective_presentation :
    ∀ M : ModuleCat.{u} R,
      ∃ (N P : ModuleCat.{u} R) (f : N ⟶ P) (g : P ⟶ M) (hzero : f ≫ g = 0),
        (ShortComplex.mk f g hzero).UniversallyExact ∧ P.PureProjective)
