/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CotangentComplex.Finiteness
import StacksCheckRecall

/-!
# Finite André-Quillen homology of finite-type algebras

Lemma 92.5.4 records that if `A` is Noetherian and `A → B` is of finite type, then every
cohomology module of the André-Quillen complex `L_{B/A}` is a finite `B`-module.
-/

@[expose] public section

universe u

/- Lemma 92.5.4. Let `A` be a Noetherian ring. Let `A → B` be a finite type ring map.
Then `H^n(L_{B/A})` is a finite `B`-module for all `n : ℤ`. -/
@[stacks 08PZ] #check (Algebra.CotangentComplex.homology_finite :
  ∀ (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [Algebra.FiniteType A B] (n : ℤ),
    Module.Finite B ((Algebra.cotangentComplex A B).homology n))

#check (Algebra.CotangentComplex.homology_finite_ringHom :
  ∀ {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) [IsNoetherianRing A] (hf : f.FiniteType) (n : ℤ),
    Module.Finite B ((RingHom.cotangentComplex f).homology n))
