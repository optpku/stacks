/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll

Adapted from MichaelStollBayreuth/EllipticCurves at
4c43c4089d2960904c0a4c1bb4668e827d80a62d.
Source fragments: SelmerGroup.lean:90-92, SelmerGroup.lean:476-479, SelmerGroup.lean:965-1015, SelmerGroup.lean:1049-1049.
Changes: extracted arithmetic dependency layers, narrowed imports, and documented ownership.
The upstream files have no per-file copyright header; repository license and author retained.
-/
module

public import ReasLib.RingTheory.DedekindDomain.SelmerGroup.Finiteness

/-!
# Selmer conditions in products and along supplied power-class equivalences

The product condition uses Mathlib's product and comap subgroups. An equivalence
of power-class groups is explicit input to `selmerGroupOfEquiv`; no finite-etale
decomposition is manufactured from a property. Finite products of the general finite
Selmer containers give finiteness after transport. Consumers include split algebras
in isogeny descent and finite power-class calculations.
-/

@[expose] public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum FractionalIdeal

open scoped nonZeroDivisors

namespace IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K]
  [IsFractionRing R K]

section Etale

variable {ι : Type*} (L : ι → Type*) [(i : ι) → Field (L i)]
  (B : (i : ι) → Type*) [(i : ι) → CommRing (B i)] [(i : ι) → IsDedekindDomain (B i)]
  [(i : ι) → Algebra (B i) (L i)] [(i : ι) → IsFractionRing (B i) (L i)]
  (S : (i : ι) → Set (HeightOneSpectrum (B i))) (n : ℕ)

/-- The product of the Selmer groups of the field factors. -/
noncomputable def selmerGroupPi : Subgroup ((i : ι) → Units.modPow (L i) n) :=
  Subgroup.pi Set.univ fun i ↦ selmerGroup (R := B i) (K := L i) (S := S i) (n := n)

lemma mem_selmerGroupPi_iff (x : (i : ι) → Units.modPow (L i) n) :
    x ∈ selmerGroupPi L B S n ↔
      ∀ i, x i ∈ selmerGroup (R := B i) (K := L i) (S := S i) (n := n) := by
  simp [selmerGroupPi, Subgroup.mem_pi]

/-- A finite product of Selmer groups is finite. -/
theorem finite_selmerGroupPi [Finite ι] [(i : ι) → Finite (ClassGroup (B i))]
    [(i : ι) → Group.FG (B i)ˣ] (hS : ∀ i, (S i).Finite) [NeZero n] :
    Finite (selmerGroupPi L B S n) := by
  have (i : ι) : Finite (selmerGroup (R := B i) (K := L i) (S := S i) (n := n)) :=
    finite_selmerGroup (B i) (L i) (S i) n (hS i)
  exact .of_injective (fun x i ↦ (⟨x.1 i, (mem_selmerGroupPi_iff L B S n x.1).mp x.2 i⟩ :
    selmerGroup (R := B i) (K := L i) (S := S i) (n := n)))
    fun x y hxy ↦ Subtype.ext <| funext fun i ↦ congrArg Subtype.val (congrFun hxy i)

variable {A : Type*} [CommRing A]

/-- The arithmetic Selmer condition transported along a supplied equivalence of power-class
groups. This definition does not construct a field decomposition or require one to be canonical. -/
noncomputable def selmerGroupOfEquiv
    (e : Units.modPow A n ≃* ((i : ι) → Units.modPow (L i) n)) :
    Subgroup (Units.modPow A n) :=
  (selmerGroupPi L B S n).comap e.toMonoidHom

lemma mem_selmerGroupOfEquiv_iff (e : Units.modPow A n ≃* ((i : ι) → Units.modPow (L i) n))
    (x : Units.modPow A n) :
    x ∈ selmerGroupOfEquiv L B S n e ↔
      ∀ i, e x i ∈ selmerGroup (R := B i) (K := L i) (S := S i) (n := n) := by
  simp [selmerGroupOfEquiv, selmerGroupPi, Subgroup.mem_pi]

/-- The Selmer subgroup transported along the supplied power-class equivalence is finite. -/
theorem finite_selmerGroupOfEquiv [Finite ι] [(i : ι) → Finite (ClassGroup (B i))]
    [(i : ι) → Group.FG (B i)ˣ] (hS : ∀ i, (S i).Finite) [NeZero n]
    (e : Units.modPow A n ≃* ((i : ι) → Units.modPow (L i) n)) :
    Finite (selmerGroupOfEquiv L B S n e) := by
  have := finite_selmerGroupPi L B S n hS
  exact .of_injective (fun x ↦ (⟨e x.1, x.2⟩ : selmerGroupPi L B S n))
    fun x y hxy ↦ Subtype.ext <| e.injective <| congrArg Subtype.val hxy

end Etale

end IsDedekindDomain

end
