/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Restrict
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.IdealSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Rank
public import ReasLib.AlgebraicGeometry.QuadricCone

/-!
# The punctured affine quadratic cone

This module records the vertex `(x, y, z)`, the punctured open `U = C \ {(x, y, z)}`,
the standard affine charts `D(x)` and `D(y)`, and the ruling invertible sheaf on `U`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory
open CategoryTheory.MonoidalCategory
open Scheme.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.QuadricCone

/-- The vertex ideal `(x, y, z)` of the affine quadratic cone. -/
def vertexIdeal (k : Type u) [CommRing k] : Ideal (coordinateRing k) :=
  Ideal.span {coord k 0, coord k 1, coord k 2}

/-- The vertex ideal is the span of the three coordinate classes. -/
theorem vertexIdeal_eq_span (k : Type u) [CommRing k] :
    vertexIdeal k = Ideal.span {coord k 0, coord k 1, coord k 2} :=
  rfl

/-- The vertex ideal `(x, y, z)` is maximal when `k` is a field. -/
instance vertexIdeal_isMaximal (k : Type u) [Field k] : (vertexIdeal k).IsMaximal := by
  let q := Ideal.Quotient.mk (Ideal.span {quadricPoly k})
  let e₀ := MvPolynomial.eval₂Hom (RingHom.id k) (fun _ : Fin 3 ↦ (0 : k))
  have hrel : ∀ p ∈ Ideal.span {quadricPoly k}, e₀ p = 0 := by
    change Ideal.span {quadricPoly k} ≤ RingHom.ker e₀
    apply Ideal.span_le.mpr
    rintro p (rfl : p = quadricPoly k)
    simp [e₀, quadricPoly, RingHom.mem_ker]
  let e : coordinateRing k →+* k := Ideal.Quotient.lift _ e₀ hrel
  have heC (a : k) : e (q (MvPolynomial.C a)) = a := by
    simp [e, q, e₀]
  have heX (i : Fin 3) : e (coord k i) = 0 := by
    simp [e, coord, e₀]
  have heXq (i : Fin 3) : e (q (MvPolynomial.X i)) = 0 := by
    simpa [coord] using heX i
  have hX (i : Fin 3) : coord k i ∈ vertexIdeal k := by
    fin_cases i <;> exact Ideal.subset_span (by simp)
  have hker : RingHom.ker e = vertexIdeal k := by
    apply le_antisymm
    · intro a ha
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
      have hpoly (p : MvPolynomial (Fin 3) k) :
          q p - q (MvPolynomial.C (e (q p))) ∈ vertexIdeal k := by
        induction p using MvPolynomial.induction_on with
        | C a =>
          simpa only [heC, sub_self] using (vertexIdeal k).zero_mem
        | add p r hp hr =>
          simpa only [map_add, add_sub_add_comm] using (vertexIdeal k).add_mem hp hr
        | mul_X p i hp =>
          simpa [coord, map_mul, heXq, heC, mul_zero, map_zero, sub_zero] using
            (vertexIdeal k).mul_mem_left (q p) (hX i)
      have ha₀ : e (q p) = 0 := ha
      simpa only [ha₀, map_zero, sub_zero] using hpoly p
    · apply Ideal.span_le.mpr
      rintro a (rfl | rfl | rfl)
      · exact heX 0
      · exact heX 1
      · exact heX 2
  rw [← hker]
  exact RingHom.ker_isMaximal_of_surjective e (fun a ↦ ⟨q (MvPolynomial.C a), heC a⟩)

/-- The closed point `(x, y, z)` of the affine quadratic cone. -/
def vertex (k : Type u) [Field k] : scheme k :=
  ⟨vertexIdeal k, (vertexIdeal_isMaximal k).isPrime⟩

/-- The prime ideal of the vertex is the span of the three coordinate classes. -/
theorem vertex_asIdeal (k : Type u) [Field k] :
    (vertex k).asIdeal = vertexIdeal k :=
  rfl

/-- The singleton consisting of the vertex is closed. -/
theorem isClosed_singleton_vertex (k : Type u) [Field k] :
    IsClosed ({vertex k} : Set (scheme k)) := by
  exact (PrimeSpectrum.isClosed_singleton_iff_isMaximal (vertex k)).mpr
    (vertexIdeal_isMaximal k)

/-- The punctured cone `U = C \ {(x, y, z)}`. -/
def puncturedOpen (k : Type u) [Field k] : (scheme k).Opens :=
  ⟨({vertex k} : Set (scheme k))ᶜ, (isClosed_singleton_vertex k).isOpen_compl⟩

/-- A point of the cone lies in the punctured open if and only if it is not the vertex. -/
theorem mem_puncturedOpen_iff_ne_vertex (k : Type u) [Field k] {x : scheme k} :
    x ∈ puncturedOpen k ↔ x ≠ vertex k := by
  rfl

/-- The basic open `D(x)` on the affine quadratic cone. -/
def chartX (k : Type u) [CommRing k] : (scheme k).Opens :=
  (scheme k).basicOpen ((ΓSpecIso (CommRingCat.of (coordinateRing k))).inv (coord k 0))

/-- The basic open `D(y)` on the affine quadratic cone. -/
def chartY (k : Type u) [CommRing k] : (scheme k).Opens :=
  (scheme k).basicOpen ((ΓSpecIso (CommRingCat.of (coordinateRing k))).inv (coord k 1))

/-- The punctured cone is the union of the basic opens `D(x)` and `D(y)`. -/
theorem puncturedOpen_eq_chartX_sup_chartY (k : Type u) [Field k] :
    puncturedOpen k = chartX k ⊔ chartY k := by
  have hxy : coord k 0 * coord k 1 = coord k 2 ^ 2 := by
    apply sub_eq_zero.mp
    change (Ideal.Quotient.mk (Ideal.span {quadricPoly k})) (quadricPoly k) = 0
    exact Ideal.Quotient.mk_singleton_self (quadricPoly k)
  apply TopologicalSpace.Opens.ext
  ext p
  change (p ∈ puncturedOpen k) ↔ p ∈ chartX k ⊔ chartY k
  rw [mem_puncturedOpen_iff_ne_vertex]
  change p ≠ vertex k ↔ p ∈ chartX k ∨ p ∈ chartY k
  rw [chartX, chartY, basicOpen_eq_of_affine, basicOpen_eq_of_affine]
  change p ≠ vertex k ↔ coord k 0 ∉ p.asIdeal ∨ coord k 1 ∉ p.asIdeal
  constructor
  · intro hp
    by_contra h
    push Not at h
    have hz : coord k 2 ∈ p.asIdeal := by
      apply p.isPrime.mem_of_pow_mem 2
      rw [← hxy]
      exact p.asIdeal.mul_mem_right _ h.1
    apply hp
    apply PrimeSpectrum.ext
    symm
    apply (vertexIdeal_isMaximal k).eq_of_le p.isPrime.ne_top
    apply Ideal.span_le.mpr
    rintro a (rfl | rfl | rfl)
    · exact h.1
    · exact h.2
    · exact hz
  · rintro (hx | hy) rfl
    · exact hx (Ideal.subset_span (by simp))
    · exact hy (Ideal.subset_span (by simp))

/-- The basic open `D(x)` is affine. -/
theorem chartX_isAffineOpen (k : Type u) [CommRing k] : IsAffineOpen (chartX k) := by
  exact (isAffineOpen_top (scheme k)).basicOpen _

/-- The basic open `D(y)` is affine. -/
theorem chartY_isAffineOpen (k : Type u) [CommRing k] : IsAffineOpen (chartY k) := by
  exact (isAffineOpen_top (scheme k)).basicOpen _

/-- The restriction of the ruling `V(x, z)` to the punctured cone. -/
def rulingOnPunctured (k : Type u) [Field k] : (puncturedOpen k).toScheme.IdealSheafData :=
  (rulingIdealSheaf k).comap (puncturedOpen k).ι

/-- The restricted ruling is an effective Cartier divisor on the punctured cone. -/
instance rulingOnPunctured_isEffectiveCartierDivisor (k : Type u) [Field k] :
    IsEffectiveCartierDivisor (rulingOnPunctured k).subschemeι :=
  sorry

/-- The invertible sheaf on the punctured cone associated to the restricted ruling. -/
def rulingSheaf (k : Type u) [Field k] : (puncturedOpen k).toScheme.Modules :=
  (rulingOnPunctured k).associatedSheaf

/-- The ruling sheaf on the punctured cone is locally free of rank one. -/
instance rulingSheaf_isFiniteLocallyFreeOfRankOne (k : Type u) [Field k] :
    Modules.IsFiniteLocallyFreeOfRank 1 (rulingSheaf k) := by
  letI : Modules.Invertible (rulingSheaf k) := by
    change Modules.Invertible ((rulingOnPunctured k).associatedSheaf)
    infer_instance
  exact Modules.isFiniteLocallyFreeOfRankOne_of_invertible (rulingSheaf k)

/-- The ruling sheaf on the punctured cone is not isomorphic to the structure sheaf. -/
theorem rulingSheaf_not_isUnitObject (k : Type u) [Field k] :
    ¬ Nonempty (rulingSheaf k ≅ 𝟙_ (puncturedOpen k).toScheme.Modules) :=
  sorry

/-- The punctured affine quadratic cone over a field admits a nontrivial invertible sheaf. -/
theorem exists_nontrivial_invertibleSheaf (k : Type u) [Field k] :
    ∃ L : (puncturedOpen k).toScheme.Modules,
      IsFiniteLocallyFreeOfRank 1 L ∧
        ¬ Nonempty (L ≅ 𝟙_ (puncturedOpen k).toScheme.Modules) := by
  exact ⟨rulingSheaf k, inferInstance, rulingSheaf_not_isUnitObject k⟩

end AlgebraicGeometry.QuadricCone
