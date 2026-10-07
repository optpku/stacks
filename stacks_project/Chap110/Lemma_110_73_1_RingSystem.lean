module

public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import ReasLib.Algebra.Category.CommRingCat.InverseSystem

/-!
# The triangle inverse system of algebras

The sequential inverse system of `k`-algebras `k[x, y] / I^{n+1}` with
`I = span {xy(x + y - 1)}`, together with its categorical limit cone and
structure maps from `k`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.StrongEffectiveness

/-- The generator `xy(x + y - 1)` of the triangle ideal in `k[x, y]`. -/
def triangleGenerator (k : Type u) [CommRing k] : MvPolynomial (Fin 2) k :=
  MvPolynomial.X 0 * MvPolynomial.X 1 * (MvPolynomial.X 0 + MvPolynomial.X 1 - 1)

/-- Unfolding of `triangleGenerator`. -/
theorem triangleGenerator_eq (k : Type u) [CommRing k] :
    triangleGenerator k =
      MvPolynomial.X 0 * MvPolynomial.X 1 * (MvPolynomial.X 0 + MvPolynomial.X 1 - 1) := sorry

/-- The triangle ideal `I = (xy(x + y - 1))` in `k[x, y]`. -/
def triangleIdeal (k : Type u) [CommRing k] : Ideal (MvPolynomial (Fin 2) k) :=
  Ideal.span {triangleGenerator k}

/-- Unfolding of `triangleIdeal`. -/
theorem triangleIdeal_eq (k : Type u) [CommRing k] :
    triangleIdeal k = Ideal.span {triangleGenerator k} := sorry

/-- The stage ring `R_n = k[x, y] / I^{n+1}`; the case `n = 0` recovers `V(I)`. -/
abbrev stageRing (k : Type u) [CommRing k] (n : ℕ) : Type u :=
  MvPolynomial (Fin 2) k ⧸ triangleIdeal k ^ (n + 1)

/-- Unfolding of `stageRing`. -/
theorem stageRing_eq (k : Type u) [CommRing k] (n : ℕ) :
    stageRing k n =
      (MvPolynomial (Fin 2) k ⧸ triangleIdeal k ^ (n + 1)) := sorry

/-- The bundled commutative ring `R_n`. -/
def stageObj (k : Type u) [CommRing k] (n : ℕ) : CommRingCat.{u} :=
  CommRingCat.of (stageRing k n)

/-- Unfolding of `stageObj`. -/
theorem stageObj_eq (k : Type u) [CommRing k] (n : ℕ) :
    stageObj k n = CommRingCat.of (stageRing k n) := sorry

/-- The canonical surjection `R_{n+1} →+* R_n` induced by `I^{n+2} ⊆ I^{n+1}`. -/
def stepHom (k : Type u) [CommRing k] (n : ℕ) :
    stageRing k (n + 1) →+* stageRing k n :=
  Ideal.Quotient.factorPowSucc (triangleIdeal k) (n + 1)

/-- Unfolding of `stepHom`. -/
theorem stepHom_eq (k : Type u) [CommRing k] (n : ℕ) :
    stepHom k n = Ideal.Quotient.factorPowSucc (triangleIdeal k) (n + 1) := sorry

/-- The successor morphism `R_{n+1} ⟶ R_n` in `CommRingCat`. -/
def stepMap_stage (k : Type u) [CommRing k] (n : ℕ) :
    stageObj k (n + 1) ⟶ stageObj k n :=
  CommRingCat.ofHom (stepHom k n)

/-- Unfolding of `stepMap_stage`. -/
theorem stepMap_stage_eq (k : Type u) [CommRing k] (n : ℕ) :
    stepMap_stage k n = CommRingCat.ofHom (stepHom k n) := sorry

/-- The sequential inverse system `(R_n)` of triangle stage rings. -/
def system (k : Type u) [CommRing k] : SequentialInverseSystem CommRingCat.{u} :=
  Functor.ofOpSequence (stepMap_stage k)

/-- Stage `n` of `system k` is the bundled triangle stage ring `R_n`. -/
theorem system_obj (k : Type u) [CommRing k] (n : ℕ) :
    (system k).obj (op n) = stageObj k n := sorry

/-- The successor map of `system k` is `stepMap_stage`. -/
theorem system_stepMap (k : Type u) [CommRing k] (n : ℕ) :
    (system k).stepMap n = stepMap_stage k n := sorry

/-- Successor transitions of `system k` are surjective. -/
theorem surjective_system (k : Type u) [CommRing k] : (system k).Surjective := sorry

/-- Kernels of successor transitions of `system k` are locally nilpotent. -/
theorem kernelLocallyNilpotent_system (k : Type u) [CommRing k] :
    (system k).KernelLocallyNilpotent := sorry

/-- The structure homomorphism `k →+* R_n` of the triangle stage algebra. -/
def algebraMap_stageHom (k : Type u) [CommRing k] (n : ℕ) : k →+* stageRing k n :=
  (Ideal.Quotient.mk (triangleIdeal k ^ (n + 1))).comp
    (algebraMap k (MvPolynomial (Fin 2) k))

/-- Unfolding of `algebraMap_stageHom`. -/
theorem algebraMap_stageHom_eq (k : Type u) [CommRing k] (n : ℕ) :
    algebraMap_stageHom k n =
      (Ideal.Quotient.mk (triangleIdeal k ^ (n + 1))).comp
        (algebraMap k (MvPolynomial (Fin 2) k)) := sorry

/-- The structure morphism `k ⟶ R_n` of the triangle stage algebra. -/
def algebraMap_stage (k : Type u) [CommRing k] (n : ℕ) :
    CommRingCat.of k ⟶ stageObj k n :=
  CommRingCat.ofHom (algebraMap_stageHom k n)

/-- Successor transitions of `system k` are morphisms of `k`-algebras. -/
theorem algebra_step (k : Type u) [CommRing k] (n : ℕ) :
    algebraMap_stage k (n + 1) ≫ stepMap_stage k n = algebraMap_stage k n := sorry

/-- Naturality of `algebraMap_stage` against successor morphisms of `system k`. -/
theorem algebraMap_stage_naturality (k : Type u) [CommRing k] (n : ℕ) :
    ((Functor.const ℕᵒᵖ).obj (CommRingCat.of k)).map (homOfLE (n.le_add_right 1)).op ≫
        algebraMap_stage k n =
      algebraMap_stage k (n + 1) ≫
        (system k).map (homOfLE (n.le_add_right 1)).op := sorry

/-- The constant `k`-algebra cone on `system k`. -/
def algebraCone (k : Type u) [CommRing k] : Cone (system k) where
  pt := CommRingCat.of k
  π := NatTrans.ofOpSequence (algebraMap_stage k) (algebraMap_stage_naturality k)

/-- A chosen limiting cone of `system k`, with vertex `R = lim R_n`. -/
def limitCone (k : Type u) [CommRing k] : LimitCone (system k) :=
  getLimitCone (system k)

/-- The structure morphism `k ⟶ lim R_n` induced by the stage algebra maps. -/
def algebraMap_limit (k : Type u) [CommRing k] :
    CommRingCat.of k ⟶ (limitCone k).cone.pt :=
  (limitCone k).isLimit.lift (algebraCone k)

/-- Cone legs `lim R_n ⟶ R_n` are morphisms of `k`-algebras. -/
theorem algebra_limit_π (k : Type u) [CommRing k] (n : ℕ) :
    algebraMap_limit k ≫ (limitCone k).cone.stageMap n = algebraMap_stage k n := sorry

end AlgebraicGeometry.GroupoidsOver.StrongEffectiveness
