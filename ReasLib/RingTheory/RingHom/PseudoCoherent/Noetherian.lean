/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Relative.Noetherian
public import ReasLib.RingTheory.RingHom.PseudoCoherent.Basic

/-!
# Pseudo-coherent ring maps over Noetherian bases

This leaf records the standard finite-type criterion for pseudo-coherent
commutative ring maps out of a Noetherian ring.

@stack 067I
-/

@[expose] public section

universe u v

namespace Algebra

/-- Lemma 15.83.3: a finite type algebra over a Noetherian commutative ring has a
pseudo-coherent structure map. -/
@[stacks 067I "finite type over a Noetherian ring"]
instance isPseudoCoherentRingMap_of_finiteType_of_isNoetherianRing
    {R : Type u} {A : Type v} [CommRing R] [IsNoetherianRing R] [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] : (algebraMap R A).IsPseudoCoherentRingMap := sorry
/- Proof strategy: use the finite-type polynomial presentation of `A`; Hilbert basis makes the
presentation ring Noetherian, so the target regular module is pseudo-coherent relative to `R` by
the Noetherian relative criterion, and the class constructor supplies the finite-type field. -/

end Algebra
