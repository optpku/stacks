module

public import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.AdicCompletion.Henselian
public import ReasLib.RingTheory.AdicCompletion.LocalMap
public import ReasLib.RingTheory.Henselian.Henselization
public import ReasLib.RingTheory.Regular.GRing
public import ReasLib.RingTheory.Regular.RingMap
public import ReasLib.RingTheory.RingHom.IndEtale.Henselian

@[expose] public section

/-!
# Henselizations inside adic completions

@stack 06LJ
@stack 0A1W

For a Noetherian local ring, the structural map to a henselization induces a
bijective map on maximal-ideal completions.  A comparison map from the
henselization to the base completion is characterized by becoming the
structural map after passage to the henselization completion.  This
characterization avoids choosing computational data from a bijectivity proof.
Domain and regularity hypotheses enter only when identifying its range.
-/

open IsLocalRing

universe u v

namespace IsHenselizationOf.Completion

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {Rh : Type v} [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]

/-- The map on maximal-ideal completions induced by the structural map to a
henselization. -/
@[stacks 06LJ "henselization map on completions"]
noncomputable def map :
    AdicCompletion (maximalIdeal R) R →+*
      AdicCompletion (maximalIdeal Rh) Rh :=
  AdicCompletion.mapLocal (algebraMap R Rh)

/-- For a Noetherian local ring, henselization induces a bijection on maximal-ideal
completions. -/
@[stacks 06LJ "(b) henselization completion isomorphism"]
theorem map_bijective [IsNoetherianRing R] :
    Function.Bijective (map (R := R) (Rh := Rh)) := sorry

/-- A henselization-to-completion algebra map is the canonical comparison
when completing it recovers the structural map of the henselization
completion. -/
@[stacks 0A1W "henselization-to-completion comparison property"]
def IsComparison
    (iota : Rh →ₐ[R] AdicCompletion (maximalIdeal R) R) : Prop :=
  (map (R := R) (Rh := Rh)).comp iota.toRingHom =
    algebraMap Rh (AdicCompletion (maximalIdeal Rh) Rh)

/-- A henselization comparison bundles an explicit algebra map to the base
completion with its canonical completion compatibility. -/
@[stacks 0A1W "bundled henselization comparison"]
structure Comparison where
  /-- The comparison algebra map. -/
  toAlgHom : Rh →ₐ[R] AdicCompletion (maximalIdeal R) R
  /-- Completing the comparison recovers the structural completion map. -/
  isComparison : IsComparison (R := R) (Rh := Rh) toAlgHom

namespace Comparison

/-- Bundle an explicit comparison map and its compatibility proof. -/
@[stacks 0A1W "henselization comparison constructor"]
def of (iota : Rh →ₐ[R] AdicCompletion (maximalIdeal R) R)
    (hiota : IsComparison (R := R) (Rh := Rh) iota) :
    Comparison (R := R) (Rh := Rh) where
  toAlgHom := iota
  isComparison := hiota

/-- The comparison map underlying `Comparison.of`. -/
@[simp, stacks 0A1W "henselization comparison constructor projection"]
theorem toAlgHom_of
    (iota : Rh →ₐ[R] AdicCompletion (maximalIdeal R) R)
    (hiota : IsComparison (R := R) (Rh := Rh) iota) :
    (of iota hiota).toAlgHom = iota := sorry

end Comparison

/-- A Noetherian local ring admits a unique comparison map from any chosen
henselization to its maximal-ideal completion. -/
@[stacks 0A1W "canonical henselization-to-completion comparison"]
theorem existsUnique_comparison [IsNoetherianRing R] :
    ∃! iota : Rh →ₐ[R] AdicCompletion (maximalIdeal R) R,
      IsComparison (R := R) (Rh := Rh) iota := sorry

namespace IsComparison

variable {iota jota : Rh →ₐ[R] AdicCompletion (maximalIdeal R) R}

/-- A comparison map becomes the structural map after passing to the
completion of the henselization. -/
theorem map_comp (hiota : IsComparison (R := R) (Rh := Rh) iota) :
    (map (R := R) (Rh := Rh)).comp iota.toRingHom =
      algebraMap Rh (AdicCompletion (maximalIdeal Rh) Rh) := sorry

/-- Two comparison maps from a henselization to the base completion are
equal. -/
@[stacks 0A1W "uniqueness of the henselization comparison"]
theorem eq [IsNoetherianRing R]
    (hiota : IsComparison (R := R) (Rh := Rh) iota)
    (hjota : IsComparison (R := R) (Rh := Rh) jota) :
    iota = jota := sorry

end IsComparison

namespace Comparison

/-- A Noetherian local ring admits a bundled comparison from any chosen
henselization to its maximal-ideal completion. -/
@[stacks 0A1W "existence of a bundled henselization comparison"]
theorem nonempty [IsNoetherianRing R] :
    Nonempty (Comparison (R := R) (Rh := Rh)) := sorry

/-- Two bundled comparisons are equal when their underlying algebra maps are
equal. -/
@[ext]
theorem ext {iota jota : Comparison (R := R) (Rh := Rh)}
    (h : iota.toAlgHom = jota.toAlgHom) : iota = jota := sorry

/-- For a Noetherian base, the bundled comparison is unique. -/
@[stacks 0A1W "uniqueness of bundled henselization comparisons"]
theorem subsingleton [IsNoetherianRing R] :
    Subsingleton (Comparison (R := R) (Rh := Rh)) := sorry

/-- Completing a bundled comparison recovers the structural map to the
completion of the henselization. -/
@[stacks 0A1W "bundled comparison compatibility", simp]
theorem map_comp (iota : Comparison (R := R) (Rh := Rh)) :
    (map (R := R) (Rh := Rh)).comp iota.toAlgHom.toRingHom =
      algebraMap Rh (AdicCompletion (maximalIdeal Rh) Rh) := sorry

/-- The map underlying a bundled comparison is injective. -/
@[stacks 0A1W "bundled henselization comparison is injective"]
theorem injective [IsNoetherianRing R]
    (iota : Comparison (R := R) (Rh := Rh)) :
    Function.Injective iota.toAlgHom := sorry

/-- The map underlying a bundled comparison is local. -/
@[stacks 0A1W "bundled henselization comparison is local"]
theorem isLocal [IsNoetherianRing R]
    (iota : Comparison (R := R) (Rh := Rh)) :
    IsLocalHom iota.toAlgHom.toRingHom := sorry

/-- The algebra, completion, locality, and injectivity properties of a
bundled comparison. -/
@[stacks 0A1W "bundled henselization comparison specification"]
theorem spec [IsNoetherianRing R]
    (iota : Comparison (R := R) (Rh := Rh)) :
    (∀ r : R, iota.toAlgHom (algebraMap R Rh r) =
      algebraMap R (AdicCompletion (maximalIdeal R) R) r) ∧
      (map (R := R) (Rh := Rh)).comp iota.toAlgHom.toRingHom =
        algebraMap Rh (AdicCompletion (maximalIdeal Rh) Rh) ∧
      IsLocalHom iota.toAlgHom.toRingHom ∧
      Function.Injective iota.toAlgHom := sorry

/-- For a Noetherian local domain with regular completion map, a bundled
comparison has image equal to the algebraic closure of the base. -/
@[stacks 0A1W "bundled comparison image equality"]
theorem range_eq [IsDomain R] [IsNoetherianRing R]
    [hreg : (algebraMap R
      (AdicCompletion (maximalIdeal R) R)).Regular]
    (iota : Comparison (R := R) (Rh := Rh)) :
    iota.toAlgHom.range =
      Subalgebra.algebraicClosure R
        (AdicCompletion (maximalIdeal R) R) := sorry

/-- For a local domain which is a G-ring, a bundled comparison has image
equal to the algebraic closure of the base. -/
@[stacks 0A1W "bundled G-ring comparison image"]
theorem range_eq_of_isGRing [IsDomain R] [IsGRing R]
    (iota : Comparison (R := R) (Rh := Rh)) :
    iota.toAlgHom.range =
      Subalgebra.algebraicClosure R
        (AdicCompletion (maximalIdeal R) R) := sorry

/-- Membership in the image of a bundled comparison is equivalent to
algebraicity when the completion map is regular. -/
@[stacks 0A1W "bundled comparison image membership"]
theorem mem_iff [IsDomain R] [IsNoetherianRing R]
    [hreg : (algebraMap R
      (AdicCompletion (maximalIdeal R) R)).Regular]
    (iota : Comparison (R := R) (Rh := Rh))
    (x : AdicCompletion (maximalIdeal R) R) :
    x ∈ iota.toAlgHom.range ↔ IsAlgebraic R x := sorry

/-- For a local domain which is a G-ring, membership in the image of a
bundled comparison is equivalent to algebraicity. -/
@[stacks 0A1W "bundled G-ring comparison membership"]
theorem mem_iff_of_isGRing [IsDomain R] [IsGRing R]
    (iota : Comparison (R := R) (Rh := Rh))
    (x : AdicCompletion (maximalIdeal R) R) :
    x ∈ iota.toAlgHom.range ↔ IsAlgebraic R x := sorry

end Comparison

end IsHenselizationOf.Completion
