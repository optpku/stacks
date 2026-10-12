/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Polynomial.Basic
public import ReasLib.RingTheory.DividedPowers.Polynomial
public import stacks_project.Chap60.«60_17_0_2»

@[expose] public section

universe u

/-- The divided-power polynomial presentation `D[z]⟨ξ⟩ / (ξ - (z^p - lam))` before
`p`-adic completion. -/
noncomputable abbrev inseparableAdjoin {D : Type u} [CommRing D] (p : ℕ) (lam : D) : Type u :=
  DPPolynomial (Polynomial D) PUnit.{u + 1} ⧸
    Ideal.span
      {DPPolynomial.X (Polynomial D) PUnit.unit -
        algebraMap (Polynomial D) (DPPolynomial (Polynomial D) PUnit.{u + 1})
          (Polynomial.X ^ p - Polynomial.C lam)}

/-- Unfolding of `inseparableAdjoin` as a quotient of `DPPolynomial`. -/
theorem inseparableAdjoin_eq {D : Type u} [CommRing D] (p : ℕ) (lam : D) :
    inseparableAdjoin p lam =
      (DPPolynomial (Polynomial D) PUnit.{u + 1} ⧸
        Ideal.span
          {DPPolynomial.X (Polynomial D) PUnit.unit -
            algebraMap (Polynomial D) (DPPolynomial (Polynomial D) PUnit.{u + 1})
              (Polynomial.X ^ p - Polynomial.C lam)}) :=
  rfl

/-- The structure map `D → D[z]⟨ξ⟩ / (ξ - (z^p - lam))`. -/
noncomputable def algebraMap_inseparableAdjoin {D : Type u} [CommRing D] (p : ℕ) (lam : D) :
    D →+* inseparableAdjoin p lam :=
  (Ideal.Quotient.mk
      (Ideal.span
        {DPPolynomial.X (Polynomial D) PUnit.unit -
          algebraMap (Polynomial D) (DPPolynomial (Polynomial D) PUnit.{u + 1})
            (Polynomial.X ^ p - Polynomial.C lam)})).comp
    ((algebraMap (Polynomial D) (DPPolynomial (Polynomial D) PUnit.{u + 1})).comp
      (algebraMap D (Polynomial D)))

/-- Evaluation of the structure map on a coefficient of `D`. -/
theorem algebraMap_inseparableAdjoin_apply {D : Type u} [CommRing D] (p : ℕ) (lam : D)
    (x : D) :
    algebraMap_inseparableAdjoin p lam x =
      Ideal.Quotient.mk _
        (algebraMap (Polynomial D) (DPPolynomial (Polynomial D) PUnit.{u + 1})
          (algebraMap D (Polynomial D) x)) :=
  rfl

/-- The source ring `D'` is the `p`-adic completion of `inseparableAdjoin p lam`. -/
noncomputable abbrev inseparableAdjoinCompletion {D : Type u} [CommRing D] (p : ℕ) (lam : D) :
    Type u :=
  AdicCompletion (Ideal.span {(p : inseparableAdjoin p lam)}) (inseparableAdjoin p lam)

/-- Unfolding of `inseparableAdjoinCompletion` as an `AdicCompletion`. -/
theorem inseparableAdjoinCompletion_eq {D : Type u} [CommRing D] (p : ℕ) (lam : D) :
    inseparableAdjoinCompletion p lam =
      AdicCompletion (Ideal.span {(p : inseparableAdjoin p lam)}) (inseparableAdjoin p lam) :=
  rfl

/-- The `p`-adic completion of divided-power differentials of `D'` over `A`. -/
noncomputable def inseparableOmega
    {A : Type u} [CommRing A] {D : Type u} [CommRing D]
    (p : ℕ) [Fact (Nat.Prime p)] (lam : D)
    (f : A →+* inseparableAdjoinCompletion p lam)
    {J : Ideal (inseparableAdjoinCompletion p lam)} (γbar : DividedPowers J) : Type u :=
  crystallineOmegaD f γbar p

/-- Unfolding of `inseparableOmega` as `crystallineOmegaD`. -/
theorem inseparableOmega_eq
    {A : Type u} [CommRing A] {D : Type u} [CommRing D]
    (p : ℕ) [Fact (Nat.Prime p)] (lam : D)
    (f : A →+* inseparableAdjoinCompletion p lam)
    {J : Ideal (inseparableAdjoinCompletion p lam)} (γbar : DividedPowers J) :
    inseparableOmega p lam f γbar = crystallineOmegaD f γbar p :=
  rfl

/-- The structure map `D → D'` through `p`-adic completion. -/
noncomputable def algebraMap_inseparableAdjoinCompletion
    {D : Type u} [CommRing D] (p : ℕ) (lam : D) :
    D →+* inseparableAdjoinCompletion p lam :=
  (algebraMap (inseparableAdjoin p lam) (inseparableAdjoinCompletion p lam)).comp
    (algebraMap_inseparableAdjoin p lam)

/-- Evaluation of the completed structure map. -/
theorem algebraMap_inseparableAdjoinCompletion_apply
    {D : Type u} [CommRing D] (p : ℕ) (lam : D) (x : D) :
    algebraMap_inseparableAdjoinCompletion p lam x =
      algebraMap (inseparableAdjoin p lam) (inseparableAdjoinCompletion p lam)
        (algebraMap_inseparableAdjoin p lam x) :=
  rfl


/-- Additive group structure on `Ω_{D'}` from the completed divided-power module. -/
noncomputable instance addCommGroup_inseparableOmega
    {A D : Type u} [CommRing A] [CommRing D]
    {p : ℕ} [Fact (Nat.Prime p)] {lam : D}
    {f : A →+* inseparableAdjoinCompletion p lam}
    {J : Ideal (inseparableAdjoinCompletion p lam)} {γbar : DividedPowers J} :
    AddCommGroup (inseparableOmega p lam f γbar) :=
  inferInstanceAs (AddCommGroup (crystallineOmegaD f γbar p))

/-- Native `D'`-module structure on `Ω_{D'}`. -/
noncomputable instance module_inseparableOmega_self
    {A D : Type u} [CommRing A] [CommRing D]
    {p : ℕ} [Fact (Nat.Prime p)] {lam : D}
    {f : A →+* inseparableAdjoinCompletion p lam}
    {J : Ideal (inseparableAdjoinCompletion p lam)} {γbar : DividedPowers J} :
    Module (inseparableAdjoinCompletion p lam) (inseparableOmega p lam f γbar) :=
  inferInstanceAs (Module (inseparableAdjoinCompletion p lam) (crystallineOmegaD f γbar p))

/-- The image of `Polynomial.X` (the source coordinate `z`) in `D'`. -/
noncomputable def inseparableZ {D : Type u} [CommRing D] (p : ℕ) (lam : D) :
    inseparableAdjoinCompletion p lam :=
  algebraMap (inseparableAdjoin p lam) (inseparableAdjoinCompletion p lam)
    (Ideal.Quotient.mk _
      (algebraMap (Polynomial D) (DPPolynomial (Polynomial D) PUnit.{u + 1}) Polynomial.X))

/-- `D`-algebra structure on the completed inseparable adjoin. -/
noncomputable instance algebra_inseparableAdjoinCompletion
    {D : Type u} [CommRing D] {p : ℕ} {lam : D} :
    Algebra D (inseparableAdjoinCompletion p lam) :=
  (algebraMap_inseparableAdjoinCompletion p lam).toAlgebra

/-- `A`-algebra structure on `D'` via `A → D → D'`. -/
noncomputable instance algebra_inseparableAdjoinCompletion_over
    {A D : Type u} [CommRing A] [CommRing D] [Algebra A D] {p : ℕ} {lam : D} :
    Algebra A (inseparableAdjoinCompletion p lam) :=
  ((algebraMap_inseparableAdjoinCompletion p lam).comp (algebraMap A D)).toAlgebra

/-- Scalar tower `A → D → D'`. -/
instance isScalarTower_inseparableAdjoinCompletion
    {A D : Type u} [CommRing A] [CommRing D] [Algebra A D] {p : ℕ} {lam : D} :
    IsScalarTower A D (inseparableAdjoinCompletion p lam) :=
  sorry
