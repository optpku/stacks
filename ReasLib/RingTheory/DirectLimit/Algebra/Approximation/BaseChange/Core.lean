/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Core stage base change for directed algebra approximations

This leaf owns the tensor-product carrier, transition algebra maps, and
computation laws for a directed ring-hom approximation.  Surjectivity,
bijectivity, and localization properties are kept in companion property
leaves.
-/

@[expose] public section

open scoped TensorProduct

universe u v w

noncomputable section

namespace Ring.DirectLimit.Algebra.Approximation.Hom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable {f : R →+* S}

/-
The algebra and scalar-tower instances below are deliberately local: they are
induced by a chosen stage map and are not canonical ambient instances for the
underlying rings.  Registering them globally would make typeclass search
ambiguous.  `baseChange` packages the resulting carrier so consumers do not
need to rebuild these pins.
-/

/-- The tensor-product source of the canonical map from a stage `i` to a later
stage `j`. -/
@[stacks 00R0 "directed ring-hom approximation base change"]
abbrev baseChange (A : Hom f) {i j : A.index} (h : i ≤ j) : Type _ :=
  let _ : Algebra (A.source i) (A.target i) := (A.map i).toAlgebra
  let _ : Algebra (A.source i) (A.source j) := (A.sourceMap i j h).toAlgebra
  A.target i ⊗[A.source i] A.source j

/-- The target transition map respects the source-stage algebra structures
selected by a transition. -/
@[stacks 00R0 "directed ring-hom approximation base change"]
theorem transitionAlgHom_commutes (A : Hom f) {i j : A.index} (h : i ≤ j) :
    let _ : Algebra (A.source i) (A.target i) := (A.map i).toAlgebra
    let _ : Algebra (A.source i) (A.target j) :=
      ((A.map j).comp (A.sourceMap i j h)).toAlgebra
    ∀ x : A.source i,
      A.targetMap i j h (algebraMap (A.source i) (A.target i) x) =
        algebraMap (A.source i) (A.target j) x := sorry

/-- The target transition map viewed as an algebra homomorphism over the
earlier source stage. -/
@[stacks 00R0 "directed ring-hom approximation base change"]
noncomputable def transitionAlgHom (A : Hom f) {i j : A.index} (h : i ≤ j) :
    let _ : Algebra (A.source i) (A.target i) := (A.map i).toAlgebra
    let _ : Algebra (A.source i) (A.target j) :=
      ((A.map j).comp (A.sourceMap i j h)).toAlgebra
    A.target i →ₐ[A.source i] A.target j :=
  let _ : Algebra (A.source i) (A.target i) := (A.map i).toAlgebra
  let _ : Algebra (A.source i) (A.target j) :=
    ((A.map j).comp (A.sourceMap i j h)).toAlgebra
  { toRingHom := A.targetMap i j h
    commutes' := A.transitionAlgHom_commutes h }

/-- Forgetting the base algebra structure on a transition algebra homomorphism
recovers the canonical target transition. -/
@[simp, stacks 00R0 "directed ring-hom approximation base change"]
theorem transitionAlgHom_hom (A : Hom f) {i j : A.index} (h : i ≤ j) :
    let _ : Algebra (A.source i) (A.target i) := (A.map i).toAlgebra
    let _ : Algebra (A.source i) (A.target j) :=
      ((A.map j).comp (A.sourceMap i j h)).toAlgebra
    (A.transitionAlgHom h).toRingHom = A.targetMap i j h := sorry

/-- A transition algebra homomorphism evaluates as the underlying target
transition. -/
@[simp, stacks 00R0 "directed ring-hom approximation base change"]
theorem transitionAlgHom_apply (A : Hom f) {i j : A.index} (h : i ≤ j)
    (x : A.target i) :
    let _ : Algebra (A.source i) (A.target i) := (A.map i).toAlgebra
    let _ : Algebra (A.source i) (A.target j) :=
      ((A.map j).comp (A.sourceMap i j h)).toAlgebra
    A.transitionAlgHom h x = A.targetMap i j h x := sorry

/-- The canonical base-change algebra homomorphism
    `target i ⊗[source i] source j →ₐ[source i] target j` attached to a
    transition `i ≤ j`. -/
@[stacks 00R0 "directed ring-hom approximation base change"]
noncomputable def baseChangeAlgHom (A : Hom f) {i j : A.index} (h : i ≤ j) :
    let _ : Algebra (A.source i) (A.target i) := (A.map i).toAlgebra
    let _ : Algebra (A.source i) (A.source j) := (A.sourceMap i j h).toAlgebra
    let _ : Algebra (A.source j) (A.target j) := (A.map j).toAlgebra
    let _ : Algebra (A.source i) (A.target j) :=
      ((A.map j).comp (A.sourceMap i j h)).toAlgebra
    let _ : IsScalarTower (A.source i) (A.source j) (A.target j) :=
      IsScalarTower.of_algebraMap_eq' rfl
    A.baseChange h →ₐ[A.source i] A.target j :=
  let _ : Algebra (A.source i) (A.target i) := (A.map i).toAlgebra
  let _ : Algebra (A.source i) (A.source j) := (A.sourceMap i j h).toAlgebra
  let _ : Algebra (A.source j) (A.target j) := (A.map j).toAlgebra
  let _ : Algebra (A.source i) (A.target j) :=
    ((A.map j).comp (A.sourceMap i j h)).toAlgebra
  let _ : IsScalarTower (A.source i) (A.source j) (A.target j) :=
    IsScalarTower.of_algebraMap_eq' rfl
  Algebra.TensorProduct.productMap (A.transitionAlgHom h)
    (IsScalarTower.toAlgHom (A.source i) (A.source j) (A.target j))

/-- The canonical base-change ring homomorphism `target i ⊗[source i] source j →+* target j`
    is the underlying map of `baseChangeAlgHom`. -/
@[stacks 00R0 "directed ring-hom approximation base change"]
noncomputable def baseChangeMap (A : Hom f) {i j : A.index} (h : i ≤ j) :
    A.baseChange h →+* A.target j :=
  let _ : Algebra (A.source i) (A.target i) := (A.map i).toAlgebra
  let _ : Algebra (A.source i) (A.source j) := (A.sourceMap i j h).toAlgebra
  let _ : Algebra (A.source j) (A.target j) := (A.map j).toAlgebra
  let _ : Algebra (A.source i) (A.target j) :=
    ((A.map j).comp (A.sourceMap i j h)).toAlgebra
  let _ : IsScalarTower (A.source i) (A.source j) (A.target j) :=
    IsScalarTower.of_algebraMap_eq' rfl
  (A.baseChangeAlgHom h).toRingHom

/-- The canonical stage base-change map evaluates on a pure tensor by
multiplying the target transition of its left factor with the later stage map
of its right factor. -/
@[simp, stacks 00R0 "directed ring-hom approximation base change"]
theorem baseChangeMap_tmul (A : Hom f) {i j : A.index} (h : i ≤ j)
    (x : A.target i) (y : A.source j) :
    let _ : Algebra (A.source i) (A.target i) := (A.map i).toAlgebra
    let _ : Algebra (A.source i) (A.source j) := (A.sourceMap i j h).toAlgebra
    let _ : Algebra (A.source j) (A.target j) := (A.map j).toAlgebra
    let _ : Algebra (A.source i) (A.target j) :=
      ((A.map j).comp (A.sourceMap i j h)).toAlgebra
    let _ : IsScalarTower (A.source i) (A.source j) (A.target j) :=
      IsScalarTower.of_algebraMap_eq' rfl
    A.baseChangeMap h (x ⊗ₜ[A.source i] y) =
      A.targetMap i j h x * A.map j y := sorry

/-- The stage base-change map sends the canonical left generator to the later
stage map. -/
@[simp, stacks 00R0 "directed ring-hom approximation base change"]
theorem baseChangeMap_one_tmul (A : Hom f) {i j : A.index} (h : i ≤ j)
    (y : A.source j) :
    let _ : Algebra (A.source i) (A.target i) := (A.map i).toAlgebra
    let _ : Algebra (A.source i) (A.source j) := (A.sourceMap i j h).toAlgebra
    let _ : Algebra (A.source j) (A.target j) := (A.map j).toAlgebra
    let _ : Algebra (A.source i) (A.target j) :=
      ((A.map j).comp (A.sourceMap i j h)).toAlgebra
    let _ : IsScalarTower (A.source i) (A.source j) (A.target j) :=
      IsScalarTower.of_algebraMap_eq' rfl
    A.baseChangeMap h (1 ⊗ₜ[A.source i] y) = A.map j y := sorry

/-- The base-change map restricts on the left tensor factor to the target
transition map. -/
@[simp, stacks 00R0 "directed ring-hom approximation base change"]
theorem baseChangeMap_comp_includeLeft (A : Hom f) {i j : A.index} (h : i ≤ j) :
    let _ : Algebra (A.source i) (A.target i) := (A.map i).toAlgebra
    let _ : Algebra (A.source i) (A.source j) := (A.sourceMap i j h).toAlgebra
    let _ : Algebra (A.source i) (A.target j) :=
      ((A.map j).comp (A.sourceMap i j h)).toAlgebra
    (A.baseChangeMap h).comp
        (Algebra.TensorProduct.includeLeft :
          A.target i →ₐ[A.source i] A.baseChange h).toRingHom =
      A.targetMap i j h := sorry

/-- The base-change map restricts on the right tensor factor to the later
stage map. -/
@[simp, stacks 00R0 "directed ring-hom approximation base change"]
theorem baseChangeMap_comp_includeRight (A : Hom f) {i j : A.index} (h : i ≤ j) :
    let _ : Algebra (A.source i) (A.target i) := (A.map i).toAlgebra
    let _ : Algebra (A.source i) (A.source j) := (A.sourceMap i j h).toAlgebra
    let _ : Algebra (A.source j) (A.target j) := (A.map j).toAlgebra
    (A.baseChangeMap h).comp
        (Algebra.TensorProduct.includeRight :
          A.source j →ₐ[A.source i] A.baseChange h).toRingHom =
      A.map j := sorry

/-- The left tensor inclusion is sent to the target transition pointwise. -/
@[simp, stacks 00R0 "directed ring-hom approximation base change"]
theorem baseChangeMap_includeLeft (A : Hom f) {i j : A.index} (h : i ≤ j)
    (x : A.target i) :
    let _ : Algebra (A.source i) (A.target i) := (A.map i).toAlgebra
    let _ : Algebra (A.source i) (A.source j) := (A.sourceMap i j h).toAlgebra
    let _ : Algebra (A.source i) (A.target j) :=
      ((A.map j).comp (A.sourceMap i j h)).toAlgebra
    A.baseChangeMap h
        ((Algebra.TensorProduct.includeLeft :
          A.target i →ₐ[A.source i] A.baseChange h) x) =
      A.targetMap i j h x := sorry

/-- The right tensor inclusion is sent to the later stage map pointwise. -/
@[simp, stacks 00R0 "directed ring-hom approximation base change"]
theorem baseChangeMap_includeRight (A : Hom f) {i j : A.index} (h : i ≤ j)
    (y : A.source j) :
    let _ : Algebra (A.source i) (A.target i) := (A.map i).toAlgebra
    let _ : Algebra (A.source i) (A.source j) := (A.sourceMap i j h).toAlgebra
    let _ : Algebra (A.source j) (A.target j) := (A.map j).toAlgebra
    A.baseChangeMap h
        ((Algebra.TensorProduct.includeRight :
          A.source j →ₐ[A.source i] A.baseChange h) y) =
      A.map j y := sorry

end Ring.DirectLimit.Algebra.Approximation.Hom
