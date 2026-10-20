/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Regular.RegularSequence
public import ReasLib.RingTheory.RegularLocalRing.Parameters.Dimension

@[expose] public section

/-!
# Derived Properties of Systems of Parameters

This module collects regular-sequence and quotient-regularity consequences of the chosen-family
parameter API.  The definitions themselves remain in `Parameters` so clients that only construct
parameter families do not import the regular-sequence development.
-/

universe u

namespace IsLocalRing

namespace IsRegularSystemOfParameters

/-- A Noetherian local ring admitting a regular system of parameters is a
regular local ring. -/
@[stacks 00NQ]
theorem isRegularLocalRing
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {d : ℕ} {x : Fin d → maximalIdeal R}
    (hx : IsRegularSystemOfParameters x) : IsRegularLocalRing R := sorry

/-- Lemma 10.106.3 (1) (Tag 00NQ): the ordered family underlying a regular system of parameters
is a regular sequence. -/
@[stacks 00NQ]
theorem isRegular
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {d : ℕ} {x : Fin d → maximalIdeal R}
    (hx : IsRegularSystemOfParameters x) :
    RingTheory.Sequence.IsRegular R (List.ofFn fun i ↦ (x i : R)) := sorry

/-- Lemma 10.106.3 (2) (Tag 00NQ): quotienting a regular local ring by the parameter ideal of
any initial segment of a regular system of parameters again gives a regular local ring. -/
@[stacks 00NQ]
theorem isRegularLocalRing_quotient_parameterIdeal
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] {d i : ℕ}
    {x : Fin d → maximalIdeal R} (hx : IsRegularSystemOfParameters x) (hi : i ≤ d) :
    IsRegularLocalRing (R ⧸ parameterIdeal (x ∘ Fin.castLE hi)) := sorry

end IsRegularSystemOfParameters

namespace IsPartOfRegularSystemOfParameters

/-- Lemma 10.106.3 (Tag 00NQ), derived partial-system form: a partial regular system is a regular
sequence because it is the prefix of the complete `Fin d`-indexed extension supplied by
`IsPartOfRegularSystemOfParameters`. -/
theorem isRegular
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {d c : ℕ} {x : Fin c → maximalIdeal R}
    (hx : IsPartOfRegularSystemOfParameters d x) :
    RingTheory.Sequence.IsRegular R (List.ofFn fun i ↦ (x i : R)) := sorry

/-- Lemma 10.106.3 (Tag 00NQ), derived partial-system form: quotienting by the parameter ideal of
a partial regular system gives a regular local ring.  The partial family is the `Fin.castLE`
prefix of its witnessed complete extension. -/
theorem isRegularLocalRing_quotient_parameterIdeal
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] {d c : ℕ}
    {x : Fin c → maximalIdeal R} (hx : IsPartOfRegularSystemOfParameters d x) :
    IsRegularLocalRing (R ⧸ parameterIdeal x) := sorry

end IsPartOfRegularSystemOfParameters

end IsLocalRing

namespace IsRegularLocalRing

/-- Tag 00NR: if a quotient of a regular local ring is regular local, then its kernel ideal is
the parameter ideal of a partial regular system of parameters. -/
@[stacks 00NR]
theorem exists_parameterIdeal_eq_of_quotient
    {R : Type u} [CommRing R] [IsRegularLocalRing R]
    (I : Ideal R) (hI : IsRegularLocalRing (R ⧸ I)) :
    ∃ (c : ℕ) (x : Fin c → IsLocalRing.maximalIdeal R),
      IsLocalRing.IsPartOfRegularSystemOfParameters
          (IsLocalRing.maximalIdeal R).spanFinrank x ∧
        IsLocalRing.parameterIdeal x = I := sorry

/-- A quotient of a regular local ring is regular local exactly when its defining ideal is the
parameter ideal of a partial regular system of parameters. -/
@[stacks 00NR "quotient characterization"]
theorem quotient_iff_exists_parameterIdeal
    {R : Type u} [CommRing R] [IsRegularLocalRing R] (I : Ideal R) :
    IsRegularLocalRing (R ⧸ I) ↔
      ∃ (c : ℕ) (x : Fin c → IsLocalRing.maximalIdeal R),
        IsLocalRing.IsPartOfRegularSystemOfParameters
            (IsLocalRing.maximalIdeal R).spanFinrank x ∧
          IsLocalRing.parameterIdeal x = I := sorry

end IsRegularLocalRing

universe v

namespace RingHom

/-- The kernel of a surjection between regular local rings is the parameter ideal of a partial
regular system of parameters in the source. -/
@[stacks 00NR "surjective kernel"]
theorem exists_parameterIdeal_eq_ker_of_surjective
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsRegularLocalRing R] [IsRegularLocalRing S]
    (f : R →+* S) (hf : Function.Surjective f) :
    ∃ (c : ℕ) (x : Fin c → IsLocalRing.maximalIdeal R),
      IsLocalRing.IsPartOfRegularSystemOfParameters
          (IsLocalRing.maximalIdeal R).spanFinrank x ∧
        IsLocalRing.parameterIdeal x = RingHom.ker f := sorry

end RingHom
