/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap88.Lemma_88_3_5_Instances
public import stacks_project.Chap88.Remark_88_2_3_Base_change_Comparison
public import stacks_project.Chap88.Remark_88_5_1_Linear_approximation_Aeval

/-!
# Same-variable completed presentations under pair base change

A Remark 88.2.3 map of pairs `(A1, I1) → (A2, I2)` and a completed polynomial
presentation of `B1` over `(A1, I1)` induce a same-variable presentation of the
completed base change `(B1 ⊗[A1] A2)^∧` over `(A2, I2)`, together with the
coefficient-extension map of completed polynomial rings.
-/

@[expose] public section

noncomputable section

universe u

open Algebra.NaiveCotangent.Adic
open Algebra.TopologicallyFiniteType
open CommAlgCat.TopologicallyFiniteType (includeLeftToCompletion)

variable {A1 A2 : Type u} [CommRing A1] [CommRing A2] [Algebra A1 A2]

namespace Algebra.TopologicallyFiniteType

/-- The `B`-algebra structure on `(B ⊗[A1] A2)^∧` induced by
`includeLeftToCompletion`. -/
instance instAlgebraLeft (I2 : Ideal A2) (B : Type u)
    [CommRing B] [Algebra A1 B] :
    Algebra B (completedBaseChange A1 I2 B) :=
  (includeLeftToCompletion I2 B).toAlgebra

/-- The structure maps `A1 → B → (B ⊗[A1] A2)^∧` form a scalar tower. -/
instance instIsScalarTowerLeft (I2 : Ideal A2) (B : Type u)
    [CommRing B] [Algebra A1 B] :
    IsScalarTower A1 B (completedBaseChange A1 I2 B) := sorry

/-- The structure maps `A1 → A2 → (B ⊗[A1] A2)^∧` form a scalar tower. -/
instance instIsScalarTowerRight (I2 : Ideal A2) (B : Type u)
    [CommRing B] [Algebra A1 B] :
    IsScalarTower A1 A2 (completedBaseChange A1 I2 B) := sorry

/-- Tuples of completed-base-change coordinates are a scalar tower for
`B → (B ⊗[A1] A2)^∧`. -/
instance instIsScalarTowerPi (I2 : Ideal A2) (B : Type u)
    [CommRing B] [Algebra A1 B] {ι : Type u} :
    IsScalarTower B (completedBaseChange A1 I2 B)
      (ι → completedBaseChange A1 I2 B) := sorry

end Algebra.TopologicallyFiniteType

namespace Algebra.NaiveCotangent.Adic

/-- Coefficient extension sends extended powers of `I1` into extended powers of
`I2`, after stretching the exponent by `c`. -/
theorem polynomialIdeal_map_pow_le_comap (I1 : Ideal A1) (I2 : Ideal A2)
    {c : ℕ} (hc : 1 ≤ c) (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2) {ι : Type u} (n : ℕ) :
    polynomialIdeal A1 I1 ι ^ (c * n) ≤
      (polynomialIdeal A2 I2 ι ^ n).comap (MvPolynomial.map (algebraMap A1 A2)) := sorry

namespace Presentation

/-- Finite-stage coefficient extension of `A1[x_ι]^∧` along `A1 → A2`, landing
in `A2[x_ι] ⧸ (I2 · A2[x_ι]) ^ n`. -/
def polynomialMapStage (I1 : Ideal A1) (I2 : Ideal A2) {c : ℕ} (hc : 1 ≤ c)
    (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2) {ι : Type u} (n : ℕ) :
    polynomialCompletion A1 I1 ι →+* MvPolynomial ι A2 ⧸ polynomialIdeal A2 I2 ι ^ n :=
  (Ideal.quotientMap (polynomialIdeal A2 I2 ι ^ n) (MvPolynomial.map (algebraMap A1 A2))
      (polynomialIdeal_map_pow_le_comap I1 I2 hc hI n)).comp
    (AdicCompletion.evalₐ (polynomialIdeal A1 I1 ι) (c * n)).toRingHom

/-- Finite-stage coefficient extensions commute with the inverse-system
transition maps. -/
theorem polynomialMapStage_compatible (I1 : Ideal A1) (I2 : Ideal A2) {c : ℕ}
    (hc : 1 ≤ c) (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2) {ι : Type u} {m n : ℕ}
    (hle : m ≤ n) :
    (Ideal.Quotient.factorPow (polynomialIdeal A2 I2 ι) hle).comp
        (polynomialMapStage I1 I2 hc hI n) =
      polynomialMapStage I1 I2 hc hI m := sorry

/-- Coefficient extension `A1[x_ι]^∧ →+* A2[x_ι]^∧` sending each indeterminate
to the corresponding indeterminate, obtained from `MvPolynomial.map` along
`algebraMap A1 A2`. -/
def polynomialMap (I1 : Ideal A1) (I2 : Ideal A2) {c : ℕ} (hc : 1 ≤ c)
    (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2) {ι : Type u} :
    polynomialCompletion A1 I1 ι →+* polynomialCompletion A2 I2 ι :=
  AdicCompletion.liftRingHom (polynomialIdeal A2 I2 ι) (polynomialMapStage I1 I2 hc hI)
    (polynomialMapStage_compatible I1 I2 hc hI)

/-- Coefficient extension sends the indeterminate `X I1 i` to `X I2 i`. -/
theorem polynomialMap_X (I1 : Ideal A1) (I2 : Ideal A2) {c : ℕ} (hc : 1 ≤ c)
    (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2) {ι : Type u} (i : ι) :
    polynomialMap I1 I2 hc hI (X I1 i) = X I2 i := sorry

variable {B1 : Type u} [CommRing B1] [Algebra A1 B1]

/-- The same-variable completed polynomial presentation of the completed base
change `(B1 ⊗[A1] A2)^∧` obtained by evaluating `A2[x_ι]^∧` at the images of
the `P`-variables along `includeLeftToCompletion`. -/
def baseChange (I1 : Ideal A1) (I2 : Ideal A2) {c : ℕ} (hc : 1 ≤ c)
    (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2) (hI2 : I2.FG)
    [Algebra.TopologicallyFiniteType I1 B1] {ι : Type u}
    (P : Presentation A1 B1 I1 ι) :
    Presentation A2 (completedBaseChange A1 I2 B1) I2 ι :=
  -- Local instance justification (search instability): TFT of completedBaseChange depends on explicit Remark 88.2.3 data `c`, `hI`, and `I2.FG`, which cannot appear in a global instance target type.
  letI : Algebra.TopologicallyFiniteType I2 (completedBaseChange A1 I2 B1) :=
    completedBaseChange_topologicallyFiniteType I2 I1 hc hI hI2 inferInstance
  { toAlgHom :=
      adicAeval I2 fun i ↦ includeLeftToCompletion I2 B1 (P.toAlgHom (X I1 i))
    surjective := sorry }

/-- The structure map of the base-changed presentation evaluates the
indeterminate `X I2 i` at the image of the corresponding `P`-variable. -/
theorem baseChange_X (I1 : Ideal A1) (I2 : Ideal A2) {c : ℕ} (hc : 1 ≤ c)
    (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2) (hI2 : I2.FG)
    [Algebra.TopologicallyFiniteType I1 B1] {ι : Type u}
    (P : Presentation A1 B1 I1 ι) (i : ι) :
    (baseChange I1 I2 hc hI hI2 P).toAlgHom (X I2 i) =
      includeLeftToCompletion I2 B1 (P.toAlgHom (X I1 i)) := sorry

/-- The base-changed presentation is a surjective `A2`-algebra map
`A2[x_ι]^∧ →ₐ[A2] (B1 ⊗[A1] A2)^∧`. -/
theorem baseChange_surjective (I1 : Ideal A1) (I2 : Ideal A2) {c : ℕ} (hc : 1 ≤ c)
    (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2) (hI2 : I2.FG)
    [Algebra.TopologicallyFiniteType I1 B1] {ι : Type u}
    (P : Presentation A1 B1 I1 ι) :
    Function.Surjective (baseChange I1 I2 hc hI hI2 P).toAlgHom := sorry

/-- The morphism of extensions induced by coefficient extension of completed
polynomial rings. -/
def toBaseChangeHom (I1 : Ideal A1) (I2 : Ideal A2) {c : ℕ} (hc : 1 ≤ c)
    (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2) (hI2 : I2.FG)
    [Algebra.TopologicallyFiniteType I1 B1] {ι : Type u}
    (P : Presentation A1 B1 I1 ι) :
    P.toExtension.Hom (baseChange I1 I2 hc hI hI2 P).toExtension where
  toRingHom := polynomialMap I1 I2 hc hI
  toRingHom_algebraMap := sorry
  algebraMap_toRingHom := sorry

/-- The underlying ring homomorphism of `toBaseChangeHom` is coefficient
extension. -/
theorem toBaseChangeHom_toRingHom (I1 : Ideal A1) (I2 : Ideal A2) {c : ℕ}
    (hc : 1 ≤ c) (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2) (hI2 : I2.FG)
    [Algebra.TopologicallyFiniteType I1 B1] {ι : Type u}
    (P : Presentation A1 B1 I1 ι) :
    (toBaseChangeHom I1 I2 hc hI hI2 P).toRingHom = polynomialMap I1 I2 hc hI := sorry

end Presentation

end Algebra.NaiveCotangent.Adic
