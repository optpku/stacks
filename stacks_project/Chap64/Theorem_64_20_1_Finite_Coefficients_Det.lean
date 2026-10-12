/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Int.Even
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Data.Int.Interval
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.RingTheory.PowerSeries.Inverse
public import stacks_project.Chap64.Proposition_64_10_2_Trace

/-!
# Determinants `det(1 - T f)` of finite-projective modules and perfect complexes

This leaf owns the reverse characteristic series `det(1 - T f)` on finite
projective modules, bounded finite-projective cochain complexes, and perfect
objects of `D(R)`, valued in `R⟦X⟧`.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory HomologicalComplex Matrix
open scoped Polynomial

namespace PowerSeries

variable {R : Type u} [CommRing R]

/-- Substitute `X ↦ X ^ d` in a formal power series. When `d = 0` this is the
constant series on the constant coefficient, matching evaluation at `X ^ 0 = 1`. -/
def substXPow (d : ℕ) (φ : PowerSeries R) : PowerSeries R :=
  if h : d = 0 then C (constantCoeff φ) else expand d h φ

/-- Unfolding of `substXPow` as `expand` for positive exponents and as the
constant series for the zero exponent. -/
theorem substXPow_spec (d : ℕ) (φ : PowerSeries R) :
    substXPow d φ =
      if h : d = 0 then C (constantCoeff φ) else expand d h φ :=
  sorry

end PowerSeries

namespace LinearMap.FiniteProjective

variable {R : Type u} [CommRing R]

/-- The reverse characteristic series `det(1 - T f)` of an endomorphism of a
finite projective module, as a formal power series. -/
def detOneSubT {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] (f : Module.End R M) :
    PowerSeries R :=
  let h := Module.Finite.exists_comp_eq_id_of_projective R M
  (charpolyRev (LinearMap.toMatrix'
      (h.choose_spec.choose_spec.choose ∘ₗ f ∘ₗ h.choose_spec.choose)) : PowerSeries R)

/-- For any splitting `pi ∘ₗ iota = LinearMap.id` of a finite projective module,
`detOneSubT f` is the reverse characteristic polynomial of `iota ∘ₗ f ∘ₗ pi`. -/
theorem detOneSubT_spec {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] {n : ℕ}
    (pi : (Fin n → R) →ₗ[R] M) (iota : M →ₗ[R] Fin n → R)
    (h_split : pi ∘ₗ iota = LinearMap.id) (f : Module.End R M) :
    detOneSubT f =
      (charpolyRev (LinearMap.toMatrix' (iota ∘ₗ f ∘ₗ pi)) : PowerSeries R) :=
  sorry

/-- The constant coefficient of `det(1 - T f)` is `1`. -/
theorem constantCoeff_detOneSubT {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] (f : Module.End R M) :
    PowerSeries.constantCoeff (detOneSubT f) = 1 :=
  sorry

/-- Conjugate endomorphisms have the same reverse characteristic series. -/
theorem detOneSubT_conjugate {M : Type v} {N : Type v}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N]
    (a : M →ₗ[R] N) (b : N →ₗ[R] M) (h_split : b ∘ₗ a = LinearMap.id)
    (f : Module.End R M) :
    detOneSubT (a ∘ₗ f ∘ₗ b) = detOneSubT f :=
  sorry

end LinearMap.FiniteProjective

namespace CochainComplex.IsBoundedFiniteProjective

variable {R : Type u} [CommRing R]
variable {P : CochainComplex (ModuleCat R) ℤ} [hP : P.IsBoundedFiniteProjective]

/-- The alternating reverse characteristic series of an endomorphism of a bounded
finite-projective cochain complex, as a formal power series. Even degrees
contribute `det(1 - T fᵢ)` and odd degrees contribute its inverse. -/
def detOneSubT (f : P ⟶ P) : PowerSeries R :=
  let h := hP.bounded
  let a := h.choose
  let b := h.choose_spec.choose
  ∏ i ∈ Finset.Icc a b,
    if Even i then
      LinearMap.FiniteProjective.detOneSubT (ModuleCat.Hom.hom (f.f i))
    else
      PowerSeries.invOfUnit
        (LinearMap.FiniteProjective.detOneSubT (ModuleCat.Hom.hom (f.f i))) 1

/-- The cochain series is the signed product of termwise reverse characteristic
series over any bounding interval. -/
theorem detOneSubT_eq_prod (f : P ⟶ P) (a b : ℤ)
    (ha : P.IsStrictlyGE a) (hb : P.IsStrictlyLE b) :
    detOneSubT f =
      ∏ i ∈ Finset.Icc a b,
        if Even i then
          LinearMap.FiniteProjective.detOneSubT (ModuleCat.Hom.hom (f.f i))
        else
          PowerSeries.invOfUnit
            (LinearMap.FiniteProjective.detOneSubT (ModuleCat.Hom.hom (f.f i))) 1 :=
  sorry

/-- The constant coefficient of the cochain series is `1`. -/
theorem constantCoeff_detOneSubT (f : P ⟶ P) :
    PowerSeries.constantCoeff (detOneSubT f) = 1 :=
  sorry

/-- Homotopic chain maps have the same reverse characteristic series. -/
theorem detOneSubT_homotopy {f g : P ⟶ P} (h_homotopy : Homotopy f g) :
    detOneSubT f = detOneSubT g :=
  sorry

/-- If `γ2 ≫ γ1` is homotopic to `𝟙 P`, conjugating an endomorphism does not
change the reverse characteristic series. -/
theorem detOneSubT_conjugate {Q : CochainComplex (ModuleCat R) ℤ}
    [Q.IsBoundedFiniteProjective] (γ1 : Q ⟶ P) (γ2 : P ⟶ Q)
    (h_homotopy : Homotopy (γ2 ≫ γ1) (𝟙 P)) (f : P ⟶ P) :
    detOneSubT (γ1 ≫ f ≫ γ2) = detOneSubT f :=
  sorry

end CochainComplex.IsBoundedFiniteProjective

namespace DerivedCategory.IsPerfect

variable {R : Type u} [CommRing R]

/-- The reverse characteristic series of an endomorphism of a perfect object of
`D(R)`, as a formal power series. -/
def detOneSubT {K : DerivedCategory (ModuleCat R)}
    (hK : DerivedCategory.IsPerfect K) (f : End K) : PowerSeries R :=
  let P := hK.choose
  let e := hK.choose_spec.choose.symm
  let instFP := hK.choose_spec.choose_spec
  let hb := instFP.bounded
  let b := hb.choose_spec.choose
  let instLE := hb.choose_spec.choose_spec.2
  -- Local instance justification (noncanonical choice): `isKProjective_of_projective` needs a chosen `IsStrictlyLE` bound, which is not unique, so it cannot be a global instance from `IsBoundedFiniteProjective`.
  haveI : P.IsStrictlyLE b := instLE
  -- Local instance justification (noncanonical choice): K-projectivity of a bounded finite-projective complex depends on that chosen `IsStrictlyLE` bound, so it is not a global instance from `IsBoundedFiniteProjective`.
  haveI : P.IsKProjective := CochainComplex.isKProjective_of_projective P b
  let g := e.hom ≫ f ≫ e.inv
  let iso := DerivedCategory.quotientCompQhIso (ModuleCat R)
  let g' := iso.hom.app P ≫ g ≫ iso.inv.app P
  let hmap := Function.surjInv
    (CochainComplex.IsKProjective.Qh_map_bijective P
      ((HomotopyCategory.quotient _ _).obj P)).surjective g'
  let fP := (HomotopyCategory.quotient _ _).preimage hmap
  @CochainComplex.IsBoundedFiniteProjective.detOneSubT _ _ P instFP fP

/-- The perfect-complex series agrees with the cochain series of some bounded
finite-projective representative. -/
theorem detOneSubT_spec {K : DerivedCategory (ModuleCat R)}
    (hK : DerivedCategory.IsPerfect K) (f : End K) :
    ∃ (P : CochainComplex (ModuleCat R) ℤ)
      (hP : P.IsBoundedFiniteProjective) (fP : P ⟶ P),
      detOneSubT hK f =
        @CochainComplex.IsBoundedFiniteProjective.detOneSubT R _ P hP fP :=
  sorry

/-- The constant coefficient of the perfect-complex series is `1`. -/
theorem constantCoeff_detOneSubT {K : DerivedCategory (ModuleCat R)}
    (hK : DerivedCategory.IsPerfect K) (f : End K) :
    PowerSeries.constantCoeff (detOneSubT hK f) = 1 :=
  sorry

/-- Conjugate endomorphisms of a perfect object have the same reverse
characteristic series. -/
theorem detOneSubT_conjugate {K L : DerivedCategory (ModuleCat R)}
    (hK : DerivedCategory.IsPerfect K) (hL : DerivedCategory.IsPerfect L)
    (e : K ≅ L) (f : End K) :
    detOneSubT hL (e.inv ≫ f ≫ e.hom) = detOneSubT hK f :=
  sorry

end DerivedCategory.IsPerfect
