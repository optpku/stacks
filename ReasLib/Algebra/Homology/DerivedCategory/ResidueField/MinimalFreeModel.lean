/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import ReasLib.Algebra.Homology.CochainComplex.Bounded.Termwise.Minus
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension
import Mathlib.Tactic.CrossRefAttribute

/-!
# Minimal free models over a local ring

The residue-field homology of a pseudo-coherent derived module determines a bounded-above free
model degree by degree, and that model is unique up to an isomorphism of complexes.

@stack 0BCC
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open ComplexShape
open IsLocalRing
open scoped DerivedTensorWithAlgebra

universe u

-- Local instance justification (instance diamond): use the standard derived-category model only
-- for the minimal free-model construction.
attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.DerivedCategory.ResidueField

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- The degree-`i` homology of the derived residue-field extension of `K`. -/
@[stacks 0BCC "Derived residue-field homology"]
abbrev homology (K : DerivedCategory (ModuleCat R)) (i : ℤ) : ModuleCat (ResidueField R) :=
  (DerivedCategory.homologyFunctor (ModuleCat (ResidueField R)) i).obj
    (K ⊗[R]^L[ResidueField R])

/-- The object property of finite free `R`-modules used by a minimal free model. -/
@[stacks 0BCC "Finite free module property"]
abbrev finiteFree : ObjectProperty (ModuleCat R) :=
  fun M => Module.Free R M ∧ Module.Finite R M

/-- Bounded-above cochain complexes of finite free `R`-modules. -/
@[stacks 0BCC "Bounded-above finite free complexes"]
abbrev BoundedFiniteFree := CochainComplex.Minus.TermsIn (finiteFree R)

/-- Lemma 15.76.6 (0BCC), finiteness clause: residue-field homology is finite-dimensional and
vanishes in all sufficiently high degrees. -/
@[stacks 0BCC "Residue-field homology finiteness"]
theorem finiteDimensional_and_eventually_isZero
    (K : DerivedCategory (ModuleCat R)) (hK : K.IsPseudoCoherent) :
    (∀ i : ℤ, FiniteDimensional (ResidueField R) (homology R K i)) ∧
      ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (homology R K i) := sorry

/-- Lemma 15.76.6 (0BCC), existence clause: prescribed residue-field homology dimensions lift to
a bounded-above finite-free representative. -/
@[stacks 0BCC "Existence of a minimal free model"]
theorem existsBoundedAboveFreeModel
    (K : DerivedCategory (ModuleCat R)) (hK : K.IsPseudoCoherent) (d : ℤ → ℕ)
    (hd : ∀ i : ℤ,
      Nonempty ((homology R K i) ≃ₗ[ResidueField R] (Fin (d i) → ResidueField R))) :
    ∃ P : BoundedFiniteFree R,
      (∀ i : ℤ,
        Nonempty (((P : CochainComplex (ModuleCat R) ℤ).X i) ≃ₗ[R] (Fin (d i) → R))) ∧
        Nonempty (K ≅ DerivedCategory.Q.obj (P : CochainComplex (ModuleCat R) ℤ)) := sorry

/-- Lemma 15.76.6 (0BCC), uniqueness clause: bounded-above free models with the prescribed ranks
are isomorphic as cochain complexes. -/
@[stacks 0BCC "Uniqueness of a minimal free model"]
theorem boundedAboveFreeModel_unique
    (K : DerivedCategory (ModuleCat R)) (d : ℤ → ℕ)
    (hd : ∀ i : ℤ,
      Nonempty ((homology R K i) ≃ₗ[ResidueField R] (Fin (d i) → ResidueField R)))
    {P P' : BoundedFiniteFree R}
    (hP : ∀ i : ℤ,
      Nonempty (((P : CochainComplex (ModuleCat R) ℤ).X i) ≃ₗ[R] (Fin (d i) → R)))
    (hPK : Nonempty (K ≅ DerivedCategory.Q.obj (P : CochainComplex (ModuleCat R) ℤ)))
    (hP' : ∀ i : ℤ,
      Nonempty (((P' : CochainComplex (ModuleCat R) ℤ).X i) ≃ₗ[R] (Fin (d i) → R)))
    (hP'K : Nonempty (K ≅ DerivedCategory.Q.obj (P' : CochainComplex (ModuleCat R) ℤ))) :
    Nonempty
      ((P : CochainComplex (ModuleCat R) ℤ) ≅
        (P' : CochainComplex (ModuleCat R) ℤ)) := sorry

end CategoryTheory.DerivedCategory.ResidueField
