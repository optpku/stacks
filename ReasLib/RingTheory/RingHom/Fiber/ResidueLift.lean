/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Ring homomorphisms lifting residue-field maps

This file packages the property that a ring homomorphism pulls a specified
target prime back to a specified source prime and induces a prescribed map
between their residue fields.
-/

@[expose] public section

universe u v w

namespace RingHom

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]

/-- A ring homomorphism is a residue lift from `p` to `q` when it pulls `q`
back to `p` and induces the prescribed residue-field map. -/
@[stacks 08HR "ring homomorphism lifting a residue-field map"]
def IsResidueLift (f : A →+* B) (p : PrimeSpectrum A) (q : PrimeSpectrum B)
    (τ : p.asIdeal.ResidueField →+* q.asIdeal.ResidueField) : Prop :=
  ∃ hpq : p.asIdeal = Ideal.comap f q.asIdeal,
    Ideal.ResidueField.map p.asIdeal q.asIdeal f hpq = τ

namespace IsResidueLift

/-- Construct a residue lift from its prime-pullback and residue-map
conditions. -/
theorem mk {f : A →+* B} {p : PrimeSpectrum A} {q : PrimeSpectrum B}
    {τ : p.asIdeal.ResidueField →+* q.asIdeal.ResidueField}
    (hpq : p.asIdeal = Ideal.comap f q.asIdeal)
    (hτ : Ideal.ResidueField.map p.asIdeal q.asIdeal f hpq = τ) :
    f.IsResidueLift p q τ := sorry

/-- A residue lift pulls its target prime back to its source prime. -/
theorem comap_eq {f : A →+* B} {p : PrimeSpectrum A} {q : PrimeSpectrum B}
    {τ : p.asIdeal.ResidueField →+* q.asIdeal.ResidueField}
    (h : f.IsResidueLift p q τ) :
    PrimeSpectrum.comap f q = p := sorry

/-- A residue lift induces its prescribed residue-field map, independently
of the proof used to identify the contracted prime. -/
theorem map_eq {f : A →+* B} {p : PrimeSpectrum A} {q : PrimeSpectrum B}
    {τ : p.asIdeal.ResidueField →+* q.asIdeal.ResidueField}
    (h : f.IsResidueLift p q τ)
    (hpq : p.asIdeal = Ideal.comap f q.asIdeal) :
    Ideal.ResidueField.map p.asIdeal q.asIdeal f hpq = τ := sorry

end IsResidueLift

namespace ResiduePoint

variable {R : Type u} {A : Type v} {S : Type w}
variable [CommRing R] [CommRing A] [CommRing S]
variable [Algebra R A] [Algebra R S]

/-- A compatible map between residue fields commutes with the two maps from
the common base ring. -/
@[stacks 08HR "compatible residue-field point"]
theorem commutes
    (p : Ideal A) [p.IsPrime] (q : Ideal S) [q.IsPrime]
    (hpq : p.under R = q.under R)
    (τ : p.ResidueField →+* q.ResidueField)
    (hτ :
      τ.comp (Ideal.ResidueField.map (p.under R) p (algebraMap R A) rfl) =
        Ideal.ResidueField.map (p.under R) q (algebraMap R S) hpq)
    (r : R) :
    τ (algebraMap A p.ResidueField (algebraMap R A r)) =
      algebraMap S q.ResidueField (algebraMap R S r) := sorry

/-- The `R`-algebra point of `A` with values in `κ(q)` induced by a compatible
residue-field map `κ(p) → κ(q)`. -/
@[stacks 08HR "residue-field point"]
noncomputable def of
    (p : Ideal A) [p.IsPrime] (q : Ideal S) [q.IsPrime]
    (hpq : p.under R = q.under R)
    (τ : p.ResidueField →+* q.ResidueField)
    (hτ :
      τ.comp (Ideal.ResidueField.map (p.under R) p (algebraMap R A) rfl) =
        Ideal.ResidueField.map (p.under R) q (algebraMap R S) hpq) :
    A →ₐ[R] q.ResidueField where
  toRingHom := τ.comp (algebraMap A p.ResidueField)
  commutes' := commutes p q hpq τ hτ

/-- A residue lift is equivalently an `R`-algebra map whose composite with the
canonical map to `κ(q)` is the compatible residue-field point. -/
@[stacks 08HR "residue lift as residue-point equality"]
theorem isResidueLift_iff_eq
    (f : A →ₐ[R] S) (p : Ideal A) [p.IsPrime] (q : Ideal S) [q.IsPrime]
    (hpq : p.under R = q.under R)
    (τ : p.ResidueField →+* q.ResidueField)
    (hτ :
      τ.comp (Ideal.ResidueField.map (p.under R) p (algebraMap R A) rfl) =
        Ideal.ResidueField.map (p.under R) q (algebraMap R S) hpq) :
    (f : A →+* S).IsResidueLift
        (⟨p, inferInstance⟩ : PrimeSpectrum A) (⟨q, inferInstance⟩ : PrimeSpectrum S) τ ↔
      ((Algebra.ofId S q.ResidueField).restrictScalars R).comp f = of p q hpq τ hτ := sorry

end ResiduePoint

end RingHom
