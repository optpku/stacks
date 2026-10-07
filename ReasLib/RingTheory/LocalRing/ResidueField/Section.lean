module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import ReasLib.FieldTheory.Separable.Generated.Properties
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Sections of residue maps

A residue section is the concrete coefficient-field map used in equal-characteristic local
algebra.  This leaf also records compatibility under a local homomorphism, without introducing a
second residue-field algebra instance.

@stack 09EZ
-/

open IsLocalRing

universe u v

namespace IsLocalRing.ResidueField

/-- A ring-theoretic section of the residue map of a local ring. -/
@[stacks 09EZ "residue-map section"]
structure Section (A : Type u) [CommRing A] [IsLocalRing A] where
  /-- The map from the residue field back to the local ring. -/
  toRingHom : ResidueField A →+* A
  /-- Composing the section with the residue map is the identity. -/
  residue_comp : (residue A).comp toRingHom = RingHom.id (ResidueField A)

namespace Section

section Basic

variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- The defining equation of a residue section. -/
@[simp, stacks 09EZ "residue-map section specification"]
theorem spec (σ : Section A) :
    (residue A).comp σ.toRingHom = RingHom.id (ResidueField A) := sorry
-- Proof strategy: return the structure field `σ.residue_comp`.

/-- Residue sections are determined by their underlying ring homomorphisms. -/
@[ext, stacks 09EZ "residue-map section extensionality"]
theorem ext {σ τ : Section A} (h : σ.toRingHom = τ.toRingHom) : σ = τ := sorry
-- Proof strategy: cases on `σ` and `τ`, use `h` on the only data field, and discharge the
-- remaining section-law fields by proof irrelevance.

/-- Having a bundled residue section is equivalent to the source-facing existence of a section
homomorphism. -/
@[stacks 09EZ "residue-map section existence specification"]
theorem nonempty_iff_exists_hom :
    Nonempty (Section A) ↔
      ∃ σ : ResidueField A →+* A,
        (residue A).comp σ = RingHom.id (ResidueField A) := sorry
-- Proof strategy: unpack a section to its underlying ring homomorphism and `spec`; conversely,
-- construct `Section.mk` from the displayed map and equation.

/-- Lemma 15.116.10 (1): a local ring of prime characteristic with nilpotent maximal ideal has a
section of its residue map. -/
@[stacks 09EZ "Lemma 15.116.10 (1)"]
theorem exists_of_isNilpotent_maximalIdeal
    {p : ℕ} [Fact p.Prime] [CharP A p]
    (h_nil : IsNilpotent (maximalIdeal A)) :
    Nonempty (Section A) := sorry
-- Proof strategy: install the canonical `ZMod p`-algebra structures on `A` and `ResidueField A`.
-- Separability of the residue field over the prime field gives formal smoothness.  Apply
-- `Algebra.FormallySmooth.liftOfSurjective` to the surjective residue map; its kernel is the
-- nilpotent maximal ideal by `ker_residue`.  Package the lifted ring hom and
-- `comp_liftOfSurjective` as a `Section`.

end Basic

section Compatible

variable {A : Type u} {A' : Type v}
variable [CommRing A] [IsLocalRing A] [CommRing A'] [IsLocalRing A']

/-- Two residue sections are compatible with a local ring homomorphism when the induced square on
the rings and their residue fields commutes. -/
@[stacks 09EZ "compatible residue-map sections"]
noncomputable def Compatible (f : A →+* A') [IsLocalHom f]
    (σ : Section A) (σ' : Section A') : Prop :=
  σ'.toRingHom.comp (ResidueField.map f) = f.comp σ.toRingHom

/-- The source-facing commuting equation for compatible residue sections. -/
@[stacks 09EZ "compatible residue-map sections specification"]
theorem compatible_iff (f : A →+* A') [IsLocalHom f]
    (σ : Section A) (σ' : Section A') :
    Compatible f σ σ' ↔
      σ'.toRingHom.comp (ResidueField.map f) = f.comp σ.toRingHom := sorry
-- Proof strategy: unfold `Compatible`; the right-hand equation is its defining proposition.

variable [Algebra A A'] [IsLocalHom (algebraMap A A')]

/-- A residue section extends compatibly across a local homomorphism when the target maximal ideal
is nilpotent and the induced residue-field extension is separable. -/
@[stacks 09EZ "compatible residue section over a nilpotent target"]
theorem exists_compatible_of_isNilpotent_maximalIdeal
    (h_nil : IsNilpotent (maximalIdeal A')) (σ : Section A)
    [Algebra.IsSeparableOver (ResidueField A) (ResidueField A')] :
    ∃ σ' : Section A', Compatible (algebraMap A A') σ σ' := sorry
-- Proof strategy: give `A'` the theorem-local `ResidueField A`-algebra structure induced by
-- `(algebraMap A A').comp σ.toRingHom`, while retaining the canonical residue-field algebra on
-- `ResidueField A'`.  Regard `residue A'` as an algebra hom, use separability to obtain formal
-- smoothness, and lift the identity across its surjective map with nilpotent kernel.  The lift law
-- gives the target section equation, and its `AlgHom.commutes` law is exactly `Compatible`.

/-- Lemma 15.116.10 (2): in the prime-characteristic nilpotent setup of the source, a chosen
residue section extends compatibly across a local homomorphism with separable residue extension. -/
@[stacks 09EZ "Lemma 15.116.10 (2)"]
theorem exists_compatible
    {p : ℕ} [Fact p.Prime] [CharP A p]
    (h_source : IsNilpotent (maximalIdeal A))
    (h_target : IsNilpotent (maximalIdeal A')) (σ : Section A)
    [Algebra.IsSeparableOver (ResidueField A) (ResidueField A')] :
    ∃ σ' : Section A', Compatible (algebraMap A A') σ σ' := sorry
-- Proof strategy: apply `exists_compatible_of_isNilpotent_maximalIdeal h_target σ`; the source
-- nilpotence hypothesis is retained because it belongs to the textbook setup but is not needed
-- once the source section `σ` has already been supplied.

end Compatible

end Section

end IsLocalRing.ResidueField
