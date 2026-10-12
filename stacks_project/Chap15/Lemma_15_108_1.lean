/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.Contraction
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.108.1 (0GS5)

@stack 0GS5
-/

-- Lemma 15.108.1 (1), localization of an etale algebra.
@[stacks 0GS5 "Lemma 15.108.1 (1)"]
#check @Ideal.comap_ne_bot_of_localization_etale

-- Lemma 15.108.1 (2), flat localization of an unramified algebra.
@[stacks 0GS5 "Lemma 15.108.1 (2)"]
#check @Ideal.comap_ne_bot_of_flat_localization_unramified

-- Lemma 15.108.1 (3), flat localization of a quasi-finite algebra.
@[stacks 0GS5 "Lemma 15.108.1 (3)"]
#check @Ideal.comap_ne_bot_of_flat_localization_quasiFinite

-- Lemma 15.108.1 (4), flat localization of an integral algebra.
@[stacks 0GS5 "Lemma 15.108.1 (4)"]
#check @Ideal.comap_ne_bot_of_flat_localization_integral

-- Lemma 15.108.1 (5), flatness and no nontrivial specialization in a fiber.
@[stacks 0GS5 "Lemma 15.108.1 (5)"]
#check @Ideal.comap_ne_bot_of_flat_fiber_specialization_eq

-- Lemma 15.108.1 (6), preservation of the generic point and no fiber specialization.
@[stacks 0GS5 "Lemma 15.108.1 (6)"]
#check @Ideal.comap_ne_bot_of_genericPoint_fiber_specialization_eq

-- Lemma 15.108.1 (7), a unique point over the generic point.
@[stacks 0GS5 "Lemma 15.108.1 (7)"]
#check @Ideal.comap_ne_bot_of_unique_genericFiber
