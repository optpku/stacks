/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Extension.Basic

/-!
# Algebra extensions from explicit sections

This file constructs an algebra extension from a specified section of a surjective algebra map.
Unlike `Algebra.Extension.ofSurjective`, the section is data supplied by the caller rather than a
witness selected from a surjectivity proof.

@stack 00FQ
-/

@[expose] public section

universe u v w

namespace Algebra.Extension

variable {R : Type u} {S : Type v} {P : Type w}
variable [CommRing R] [CommRing S] [CommRing P] [Algebra R S] [Algebra R P]

/-- Construct an algebra extension from an algebra map and a specified set-theoretic section.

The local algebra pin is used only to construct the Prop-valued scalar-tower field; the `σ` field
is definitionally the supplied section. -/
@[stacks 00FQ "algebra extension from an explicit section"]
def ofSection (f : P →ₐ[R] S) (σ : S → P)
    (σ_spec : ∀ s, f (σ s) = s) : Extension R S where
  Ring := P
  algebra₂ := f.toAlgebra
  isScalarTower := by
    -- Local instance justification (noncanonical choice): the source algebra
    -- structure on `S` is determined by the explicit map `f`.
    letI := f.toAlgebra
    exact IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  σ := σ
  algebraMap_σ := σ_spec

/-- The chosen section of `ofSection` is definitionally the supplied section. -/
@[simp, stacks 00FQ "explicit extension section"]
theorem ofSection_σ (f : P →ₐ[R] S) (σ : S → P)
    (σ_spec : ∀ s, f (σ s) = s) :
    (ofSection f σ σ_spec).σ = σ :=
  rfl

/-- The structure map of an extension made from an explicit section is the
supplied algebra map. -/
@[simp, stacks 00FQ "explicit extension structure map"]
theorem toAlgHom_ofSection (f : P →ₐ[R] S) (σ : S → P)
    (σ_spec : ∀ s, f (σ s) = s) :
    IsScalarTower.toAlgHom R (ofSection f σ σ_spec).Ring S = f :=
  rfl

/-- The kernel of an extension made from an explicit section is the kernel of
the supplied algebra map. -/
@[simp, stacks 00FQ "explicit extension kernel"]
theorem ker_ofSection (f : P →ₐ[R] S) (σ : S → P)
    (σ_spec : ∀ s, f (σ s) = s) :
    (ofSection f σ σ_spec).ker = RingHom.ker f.toRingHom :=
  rfl

end Algebra.Extension
