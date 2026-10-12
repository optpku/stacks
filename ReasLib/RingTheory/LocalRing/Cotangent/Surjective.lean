/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Ideal.Cotangent
import ReasLib.RingTheory.Ideal.Nakayama.Basic
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Surjectivity from residue fields and cotangent spaces

For a finite local algebra, surjectivity on residue fields and cotangent
spaces forces the algebra map to be surjective.  The cotangent-space map is
named separately so that downstream statements do not have to expose the
underlying ideals and their comap proof.

@stack 0E8M
-/

noncomputable section

universe u v

open Ideal IsLocalRing

namespace IsLocalRing.CotangentSpace

variable {A : Type u} {B : Type v}
variable [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
variable [Algebra A B] [IsLocalHom (algebraMap A B)]

/-- The map on cotangent spaces induced by the structure map of a local algebra. -/
@[stacks 0E8M "cotangent-space map of a local algebra"]
def map (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)] :
    CotangentSpace A →ₗ[A] CotangentSpace B :=
  Ideal.mapCotangent (maximalIdeal A) (maximalIdeal B) (Algebra.ofId A B)
    (maximalIdeal_comap (algebraMap A B)).symm.le

/-- The local cotangent-space map sends the class of an element to the class
of its image under the algebra map. -/
@[simp, stacks 0E8M "cotangent-space map on generators"]
theorem map_toCotangent (x : maximalIdeal A) :
    map A B ((maximalIdeal A).toCotangent x) =
      (maximalIdeal B).toCotangent
        ⟨algebraMap A B x,
          (maximalIdeal_comap (algebraMap A B)).symm.le x.2⟩ :=
  rfl

private theorem quotientMap_surjective_of_map_surjective
    (hcot : Function.Surjective (map A B)) :
    Function.Surjective
      ((Submodule.inclusion (IsLocalRing.map_maximalIdeal_le (algebraMap A B))).quotientMapByIdeal
        (maximalIdeal B)) := by
  intro x
  obtain ⟨y, hy⟩ := hcot x
  obtain ⟨a, rfl⟩ := (maximalIdeal A).toCotangent_surjective y
  let aI : Ideal.map (algebraMap A B) (maximalIdeal A) :=
    ⟨algebraMap A B a, Ideal.mem_map_of_mem (algebraMap A B) a.2⟩
  refine ⟨Submodule.Quotient.mk aI, ?_⟩
  have himage :
      (maximalIdeal B).toCotangent
          ⟨algebraMap A B a, (maximalIdeal_comap (algebraMap A B)).symm.le a.2⟩ = x := by
    simpa using (map_toCotangent (B := B) a).trans hy
  rw [LinearMap.quotientMapByIdeal_apply_mk]
  change (maximalIdeal B).toCotangent ⟨algebraMap A B a, _⟩ = x
  simpa using himage

/-- If the target maximal ideal is finitely generated, surjectivity on
cotangent spaces forces the source maximal ideal to generate the target
maximal ideal. -/
@[stacks 0E8M "cotangent surjectivity controls the maximal ideal"]
theorem map_maximalIdeal_eq (hfg : (maximalIdeal B).FG)
    (hcot : Function.Surjective (map A B)) :
    Ideal.map (algebraMap A B) (maximalIdeal A) = maximalIdeal B := by
  let ι : Ideal.map (algebraMap A B) (maximalIdeal A) →ₗ[B] maximalIdeal B :=
    Submodule.inclusion (IsLocalRing.map_maximalIdeal_le (algebraMap A B))
  have hquot : Function.Surjective (ι.quotientMapByIdeal (maximalIdeal B)) :=
    quotientMap_surjective_of_map_surjective (A := A) (B := B) hcot
  -- Local instance justification (proof-local temporary data): Nakayama consumes finite
  -- generation of the target maximal ideal through the standard `Module.Finite` interface.
  letI : Module.Finite B (maximalIdeal B) := Module.Finite.of_fg hfg
  have hsurj : Function.Surjective ι := by
    refine LinearMap.surjective_of_quotientMapByIdeal_surjective_of_le_jacobson
      ι (maximalIdeal B) hquot ?_
    simp [IsLocalRing.ringJacobson_eq_maximalIdeal]
  apply le_antisymm (IsLocalRing.map_maximalIdeal_le (algebraMap A B))
  intro x hx
  obtain ⟨y, hy⟩ := hsurj ⟨x, hx⟩
  have hy_val : y.1 = x := congrArg Subtype.val hy
  simpa [hy_val] using y.2

private theorem quotientMap_surjective_of_residueFieldMap_surjective
    (hres : Function.Surjective (ResidueField.map (algebraMap A B)))
    (hmap : Ideal.map (algebraMap A B) (maximalIdeal A) = maximalIdeal B) :
    Function.Surjective ((Algebra.linearMap A B).quotientMapByIdeal (maximalIdeal A)) := by
  have hsmul :
      maximalIdeal A • (⊤ : Submodule A B) =
        Submodule.restrictScalars A (Ideal.map (algebraMap A B) (maximalIdeal A)) := by
    simp [Ideal.smul_top_eq_map]
  let e₁ :
      (B ⧸ (maximalIdeal A • (⊤ : Submodule A B))) ≃ₗ[A]
        (B ⧸ Submodule.restrictScalars A (Ideal.map (algebraMap A B) (maximalIdeal A))) :=
    Submodule.quotEquivOfEq _ _ hsmul
  let e₂ :
      B ⧸ Submodule.restrictScalars A (Ideal.map (algebraMap A B) (maximalIdeal A)) →
        ResidueField B :=
    Ideal.quotEquivOfEq hmap
  have he₂inj : Function.Injective e₂ := (Ideal.quotEquivOfEq hmap).injective
  intro x
  obtain ⟨y, hy⟩ := hres (e₂ (e₁ x))
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hquotientMap :
      ((Algebra.linearMap A B).quotientMapByIdeal (maximalIdeal A)) (Submodule.Quotient.mk a) =
        (Submodule.Quotient.mk (algebraMap A B a) :
          B ⧸ (maximalIdeal A • (⊤ : Submodule A B))) := by
    rfl
  have htransport :
      e₁
          (((Algebra.linearMap A B).quotientMapByIdeal (maximalIdeal A))
            (Submodule.Quotient.mk a)) =
        (Submodule.Quotient.mk (algebraMap A B a) :
          B ⧸ Submodule.restrictScalars A
            (Ideal.map (algebraMap A B) (maximalIdeal A))) := by
    rw [hquotientMap]
    simp [e₁]
  have hleft :
      e₂
          (e₁
            (((Algebra.linearMap A B).quotientMapByIdeal (maximalIdeal A))
              (Submodule.Quotient.mk a))) =
        ResidueField.map (algebraMap A B) (residue A a) := by
    rw [htransport]
    calc
      e₂ (Submodule.Quotient.mk (algebraMap A B a))
          = residue B (algebraMap A B a) := by
              change
                Ideal.quotEquivOfEq hmap
                    (Ideal.Quotient.mk _ (algebraMap A B a)) =
                  Ideal.Quotient.mk _ (algebraMap A B a)
              exact Ideal.quotEquivOfEq_mk hmap (algebraMap A B a)
      _ = ResidueField.map (algebraMap A B) (residue A a) := by
            symm
            exact IsLocalRing.ResidueField.map_residue (algebraMap A B) a
  have hy' :
      e₂
          (e₁
            (((Algebra.linearMap A B).quotientMapByIdeal (maximalIdeal A))
              (Submodule.Quotient.mk a))) = e₂ (e₁ x) :=
    hleft.trans hy
  refine ⟨Submodule.Quotient.mk a, ?_⟩
  apply e₁.injective
  exact he₂inj hy'

/-- A finite local algebra map is surjective when it is surjective on residue
fields and cotangent spaces and the target maximal ideal is finitely
generated. -/
@[stacks 0E8M "finite local algebra surjectivity criterion"]
theorem algebraMap_surjective (hf : Module.Finite A B) (hfg : (maximalIdeal B).FG)
    (hres : Function.Surjective (ResidueField.map (algebraMap A B)))
    (hcot : Function.Surjective (map A B)) :
    Function.Surjective (algebraMap A B) := by
  have hmap := map_maximalIdeal_eq (A := A) (B := B) hfg hcot
  have hquot :
      Function.Surjective ((Algebra.linearMap A B).quotientMapByIdeal (maximalIdeal A)) :=
    quotientMap_surjective_of_residueFieldMap_surjective (A := A) (B := B) hres hmap
  -- Local instance justification (proof-local temporary data): the explicit finiteness
  -- hypothesis is passed to Nakayama through its canonical typeclass interface.
  letI : Module.Finite A B := hf
  refine LinearMap.surjective_of_quotientMapByIdeal_surjective_of_le_jacobson
    (Algebra.linearMap A B) (maximalIdeal A) hquot ?_
  simp [IsLocalRing.ringJacobson_eq_maximalIdeal]

end IsLocalRing.CotangentSpace
