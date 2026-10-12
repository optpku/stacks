/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.RingTheory.Noetherian.Basic
public import ReasLib.CategoryTheory.Abelian.Projective.Ext

@[expose] public section

/-!
# Projectivity detected by degree-one Ext

@stack 05CF
@stack 0G8T
-/

open CategoryTheory

universe u v

namespace Module.Projective

variable {R : Type u} [Ring R] [Small.{v} R]

/-- Tag 05CF: an `R`-module is projective exactly when every degree-one extension out of its
associated object of `ModuleCat R` is trivial. -/
@[stacks 05CF]
theorem iff_subsingleton_ext_one (P : Type v) [AddCommGroup P] [Module R P] :
    Module.Projective R P ↔
      ∀ Y : ModuleCat.{v} R,
        Subsingleton (Abelian.Ext (ModuleCat.of R P) Y 1) := sorry

/-- Lemma 10.77.3: over a Noetherian ring, a finite module is projective if its degree-one
extensions by every finite module vanish. -/
@[stacks 0G8T]
theorem of_ext_one_vanishing_on_finite
    {R : Type u} [CommRing R] [IsNoetherianRing R] [Small.{v} R]
    {P : Type v} [AddCommGroup P] [Module R P] [Module.Finite R P]
    (hExt :
      ∀ (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M],
        Subsingleton (Abelian.Ext (ModuleCat.of R P) (ModuleCat.of R M) 1)) :
    Module.Projective R P := sorry

end Module.Projective
