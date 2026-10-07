module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.FieldTheory.Frobenius.Subfield
public import ReasLib.RingTheory.Excellent

@[expose] public section

universe u

open IsLocalRing
open FieldExtension.Frobenius

variable {A : Type u} [CommRing A]
variable {p : ℕ} [Fact p.Prime] [CharP A p]

namespace AdicCompletion

section

variable [IsNoetherianRing A] [IsLocalRing A] [CharP (ResidueField A) p]
variable [FiniteDimensional (subfield p (ResidueField A)) (ResidueField A)]

/-- Lemma 110.44.2 (1): the canonical map from a Noetherian local ring of prime
characteristic `p` with `[κ : κ ^ p] < ∞` to its completion is flat. -/
@[stacks 0G66]
theorem algebraMap_flat :
    (algebraMap A (AdicCompletion (maximalIdeal A) A)).Flat := sorry

/-- Lemma 110.44.2 (2): the canonical map from a Noetherian local ring of prime
characteristic `p` with `[κ : κ ^ p] < ∞` to its completion is formally unramified. -/
@[stacks 0G66]
instance instFormallyUnramified :
    Algebra.FormallyUnramified A (AdicCompletion (maximalIdeal A) A) := sorry

end

section

variable [IsRegularLocalRing A] [CharP (ResidueField A) p]
variable [FiniteDimensional (subfield p (ResidueField A)) (ResidueField A)]

/-- Lemma 110.44.2 (3): if `A` is regular but not excellent, then the canonical map to the
completion is not formally étale. -/
@[stacks 0G66]
theorem algebraMap_not_formallyEtale_of_not_isExcellentRing
    (h_not_excellent : ¬ IsExcellentRing.{u, u} A) :
    ¬ Algebra.FormallyEtale A (AdicCompletion (maximalIdeal A) A) := sorry

end

end AdicCompletion
