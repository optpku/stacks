/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RingTheory.AdicCompletion.Exactness
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.AdicCompletion.Exactness

/-!
# Adic completion of module short complexes

This leaf packages the objectwise `I`-adic completion of a short complex of
modules.  The finite Noetherian exactness criterion is separated from the
flat-cokernel criterion in `Exactness.ShortComplex.Flat`.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AdicCompletion

variable {R : Type u} [CommRing R]

/-- The completed structure maps of a module short complex still have zero composite. -/
@[stacks 00MA "zero composite for a completed short complex"]
theorem map_comp_eq_zero_of_shortComplex
    (I : Ideal R) (S : ShortComplex (ModuleCat.{u} R)) :
    (map I S.g.hom).comp (map I S.f.hom) = 0 := sorry

/-- The short complex of `I`-adic completions induced by a short complex of `R`-modules. -/
@[stacks 00MA "short complex induced by adic completion"]
noncomputable def mapShortComplex
    (I : Ideal R) (S : ShortComplex (ModuleCat.{u} R)) :
    ShortComplex (ModuleCat.{u} (AdicCompletion I R)) :=
  ShortComplex.moduleCatMk (map I S.f.hom) (map I S.g.hom)
    (map_comp_eq_zero_of_shortComplex I S)

/-- Over a Noetherian ring, completion preserves short exact sequences whose middle term is
finite. -/
@[stacks 00MA "adic completion of a finite short exact sequence"]
theorem mapShortComplex_shortExact_of_finite
    (I : Ideal R) [IsNoetherianRing R] {S : ShortComplex (ModuleCat.{u} R)}
    [Module.Finite R S.X₂] (hS : S.ShortExact) :
    (mapShortComplex I S).ShortExact := sorry

end AdicCompletion
