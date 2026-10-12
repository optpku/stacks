/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.RingHom.PurelyInseparable
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.RingHom.BaseChange

/-!
# Purely inseparable residue-field extensions

This leaf owns the pointwise residue-field predicate for a ring homomorphism.  The
predicate is independent of a particular chapter proof; chapter entries only package
the hypotheses needed for a source-facing theorem.
-/

@[expose] public section

open PrimeSpectrum
open scoped TensorProduct

universe u v w

namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

namespace ResidueField

/-- The residue-field map at a target prime is purely inseparable over its contracted prime. -/
@[stacks 0BRB "pointwise residue-field criterion"]
def IsPurelyInseparableAt (f : R →+* S) (q : PrimeSpectrum S) : Prop :=
  (Ideal.ResidueField.map (PrimeSpectrum.comap f q).asIdeal q.asIdeal f rfl).IsPurelyInseparable

namespace IsPurelyInseparableAt

/-- The pointwise predicate gives the canonical purely inseparable residue-field map. -/
theorem map_isPurelyInseparable
    {f : R →+* S} {q : PrimeSpectrum S}
    (h : ResidueField.IsPurelyInseparableAt f q) :
    (Ideal.ResidueField.map (PrimeSpectrum.comap f q).asIdeal q.asIdeal f rfl).IsPurelyInseparable :=
  sorry

/-- The pointwise predicate is independent of the chosen name for the contracted prime. -/
theorem map_isPurelyInseparable_of_comap_eq
    {f : R →+* S} {q : PrimeSpectrum S}
    (h : ResidueField.IsPurelyInseparableAt f q) {p : PrimeSpectrum R}
    (hp : p.asIdeal = Ideal.comap f q.asIdeal) :
    (Ideal.ResidueField.map p.asIdeal q.asIdeal f hp).IsPurelyInseparable := sorry

end IsPurelyInseparableAt

/-- A ring homomorphism has purely inseparable residue-field maps at every target prime. -/
@[stacks 0BRB "purely inseparable residue-field maps"]
def MapsPurelyInseparable (f : R →+* S) : Prop :=
  ∀ q : PrimeSpectrum S, ResidueField.IsPurelyInseparableAt f q

namespace MapsPurelyInseparable

/-- The bundled predicate evaluated at a target prime. -/
theorem atPrime
    {f : R →+* S} (h : ResidueField.MapsPurelyInseparable f) (q : PrimeSpectrum S) :
    ResidueField.IsPurelyInseparableAt f q := h q

/-- The bundled predicate gives the canonical purely inseparable residue-field map. -/
theorem map_isPurelyInseparable
    {f : R →+* S} (h : ResidueField.MapsPurelyInseparable f) (q : PrimeSpectrum S) :
    (Ideal.ResidueField.map (PrimeSpectrum.comap f q).asIdeal q.asIdeal f rfl).IsPurelyInseparable :=
  sorry

/-- The bundled predicate can be expressed using an independently named contracted prime. -/
theorem map_isPurelyInseparable_of_comap_eq
    {f : R →+* S} (h : ResidueField.MapsPurelyInseparable f)
    (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap f q = p) :
    (Ideal.ResidueField.map p.asIdeal q.asIdeal f
      (congrArg PrimeSpectrum.asIdeal hq).symm).IsPurelyInseparable := sorry

/-- The residue-field property is stable under a composite whose middle spectrum map and induced
residue-field maps are bijective. -/
theorem of_comp_bijective_middle
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    (g₁ : A →+* B) (g₂ : B →+* C)
    (hmidBij : Function.Bijective (PrimeSpectrum.comap g₂))
    (hmidRes : ∀ q : PrimeSpectrum C,
      Function.Bijective
        (Ideal.ResidueField.map (PrimeSpectrum.comap g₂ q).asIdeal q.asIdeal g₂ rfl))
    (hcomp : ResidueField.MapsPurelyInseparable (g₂.comp g₁)) :
    ResidueField.MapsPurelyInseparable g₁ := sorry

namespace BaseChange

/-- Injectivity on prime spectra and purely inseparable residue fields persist after
tensor-product base change for the canonical algebra map.  This is the primary shared owner:
the ambient `Algebra R S` instance is retained, so the tensor product in the conclusion is
definitionally the one used by consumers. -/
@[stacks 0BRB]
theorem injective_comap
    {R' : Type w} [CommRing R'] [Algebra R S] [Algebra R R']
    (hinj : Function.Injective (PrimeSpectrum.comap (algebraMap R S)))
    (hres : ResidueField.MapsPurelyInseparable (algebraMap R S)) :
    let f' : R' →+* R' ⊗[R] S := algebraMap R' (R' ⊗[R] S)
    Function.Injective (PrimeSpectrum.comap f') ∧
      ResidueField.MapsPurelyInseparable f' := sorry

/-- Ring-hom presentation of the base-change owner along an arbitrary base map. This is the
instance-free primary form: both algebra structures are induced internally by the two ring maps. -/
@[stacks 0BRB]
theorem injective_comap_of_ringHoms
    {R' : Type w} [CommRing R'] (f : R →+* S) (g : R →+* R')
    (hinj : Function.Injective (PrimeSpectrum.comap f))
    (hres : ResidueField.MapsPurelyInseparable f) :
    Function.Injective (PrimeSpectrum.comap (f.baseChange g)) ∧
      ResidueField.MapsPurelyInseparable (f.baseChange g) := sorry

end BaseChange

end MapsPurelyInseparable

end ResidueField

end RingHom
