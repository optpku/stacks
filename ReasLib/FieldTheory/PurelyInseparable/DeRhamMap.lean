/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.FieldTheory.PurelyInseparable.HigherTrace
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Restrict

@[expose] public section

noncomputable section

open Polynomial
open scoped TensorProduct
open CategoryTheory

universe u

namespace PurelyInseparableTrace.Higher

variable (p : ℕ) (hp : p.Prime)
variable (Λ R S : Type u) [CommRing Λ] [CommRing R] [CommRing S]
variable [Algebra (ZMod p) Λ] [Algebra (ZMod p) R] [Algebra Λ R]
variable [IsScalarTower (ZMod p) Λ R] [Nontrivial R]
variable [Algebra R S] [Algebra Λ S] [IsScalarTower Λ R S]
variable (a : R) (e : S ≃ₐ[R] AdjoinRoot (X ^ p - C a))

/-- The higher trace with its wrapped source identified with the canonical relative-form module. -/
noncomputable def traceOfEquivAsPlain (p : ℕ) (hp : p.Prime)
    (Λ R S : Type u) [CommRing Λ] [CommRing R] [CommRing S]
    [Algebra (ZMod p) Λ] [Algebra (ZMod p) R] [Algebra Λ R]
    [IsScalarTower (ZMod p) Λ R] [Nontrivial R]
    [Algebra R S] [Algebra Λ S] [IsScalarTower Λ R S]
    (a : R) (e : S ≃ₐ[R] AdjoinRoot (X ^ p - C a)) (n : ℕ) :
    KaehlerDifferential.DeRham.Form Λ S n →ₗ[R]
      KaehlerDifferential.DeRham.Form Λ R n :=
  LinearMap.mk
    ((traceOfEquiv (Λ := Λ) (R := R) p hp a e n).toAddMonoidHom.comp
      (RestrictScalars.addEquiv R S
        (KaehlerDifferential.DeRham.Form Λ S n)).symm.toAddMonoidHom)
    sorry

/-- The degree-`n` component obtained from the higher trace by scalar restriction. -/
noncomputable def deRhamComponent (p : ℕ) (hp : p.Prime)
    (Λ R S : Type u) [CommRing Λ] [CommRing R] [CommRing S]
    [Algebra (ZMod p) Λ] [Algebra (ZMod p) R] [Algebra Λ R]
    [IsScalarTower (ZMod p) Λ R] [Nontrivial R]
    [Algebra R S] [Algebra Λ S] [IsScalarTower Λ R S]
    (a : R) (e : S ≃ₐ[R] AdjoinRoot (X ^ p - C a)) (n : ℕ) :
    (KaehlerDifferential.DeRham.complex Λ S).X n ⟶
      (KaehlerDifferential.DeRham.complex Λ R).X n :=
  ((ModuleCat.RestrictScalars.identityIso (R := Λ) (S := S)
      (KaehlerDifferential.DeRham.Form Λ S n)).hom ≫
    (ModuleCat.ofHom
      ((traceOfEquivAsPlain p hp Λ R S a e n).restrictScalars Λ) :
      ModuleCat.of Λ (KaehlerDifferential.DeRham.Form Λ S n) ⟶
        ModuleCat.of Λ (KaehlerDifferential.DeRham.Form Λ R n)) ≫
      (ModuleCat.RestrictScalars.identityIso (R := Λ) (S := R)
        (KaehlerDifferential.DeRham.Form Λ R n)).inv)

/-- The canonical map of relative de Rham complexes whose degreewise components are the higher traces. -/
noncomputable def deRhamMap (p : ℕ) (hp : p.Prime)
    (Λ R S : Type u) [CommRing Λ] [CommRing R] [CommRing S]
    [Algebra (ZMod p) Λ] [Algebra (ZMod p) R] [Algebra Λ R]
    [IsScalarTower (ZMod p) Λ R] [Nontrivial R]
    [Algebra R S] [Algebra Λ S] [IsScalarTower Λ R S]
    (a : R) (e : S ≃ₐ[R] AdjoinRoot (X ^ p - C a)) :
    KaehlerDifferential.DeRham.complex Λ S ⟶
      KaehlerDifferential.DeRham.complex Λ R where
  f n := deRhamComponent p hp Λ R S a e n
  comm' i j hij := sorry

/-- The degree-`n` component of `deRhamMap` is the scalar-restricted higher trace. -/
theorem deRhamMap_component (n : ℕ) :
    (deRhamMap p hp Λ R S a e).f n =
      deRhamComponent p hp Λ R S a e n := sorry

/-- Evaluation of the degree-`n` component of `deRhamMap` is the higher trace. -/
theorem deRhamMap_apply (n : ℕ)
    (ω : KaehlerDifferential.DeRham.Form Λ S n) :
    (deRhamMap p hp Λ R S a e).f n ω =
      traceOfEquiv (Λ := Λ) (R := R) p hp a e n ω := sorry

/-- The degree-zero component of `deRhamMap` vanishes. -/
theorem deRhamMap_degreeZero :
    (deRhamMap p hp Λ R S a e).f 0 = 0 := sorry

/-- The map `deRhamMap` is compatible with wedge multiplication by a form from `R`. -/
theorem deRhamMap_wedge (i j : ℕ)
    (η : KaehlerDifferential.DeRham.Form Λ R i)
    (ω : KaehlerDifferential.DeRham.Form Λ S j) :
    (deRhamMap p hp Λ R S a e).f (i + j)
        (KaehlerDifferential.DeRham.formWedge Λ S i j
          (pullback i η ⊗ₜ ω)) =
      KaehlerDifferential.DeRham.formWedge Λ R i j
        (η ⊗ₜ (deRhamMap p hp Λ R S a e).f j ω) := sorry

end PurelyInseparableTrace.Higher
