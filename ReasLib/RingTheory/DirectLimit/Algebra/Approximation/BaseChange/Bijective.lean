/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.BaseChange.Core
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Bijective stage base change

This leaf contains only the surjective, injective, and bijective predicates for
the canonical stage base-change map.  Localization properties live in
`BaseChange.Properties`, so module-system and colimit consumers can import
this file without pulling in the essential-finiteness layer.
-/

@[expose] public section

open scoped TensorProduct

universe u v w

noncomputable section

namespace Ring.DirectLimit.Algebra.Approximation.Hom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable {f : R →+* S}

/-- Every transition base-change map in a directed approximation is
surjective. -/
@[stacks 00R0 "directed ring-hom approximation base change"]
def baseChange_surjective (A : Hom f) : Prop :=
  ∀ {i j : A.index} (h : i ≤ j), Function.Surjective (A.baseChangeMap h)

/-- Read the surjectivity of one transition base-change map. -/
@[stacks 00R0 "directed ring-hom approximation base change"]
theorem baseChange_surjective_at (A : Hom f)
    (hA : A.baseChange_surjective) {i j : A.index} (h : i ≤ j) :
    Function.Surjective (A.baseChangeMap h) := sorry

/-- Every transition base-change map in a directed approximation is
bijective. -/
@[stacks 00R0 "directed ring-hom approximation base change"]
def baseChange_bijective (A : Hom f) : Prop :=
  ∀ {i j : A.index} (h : i ≤ j), Function.Bijective (A.baseChangeMap h)

/-- Read the bijectivity of one transition base-change map. -/
@[stacks 00R0 "directed ring-hom approximation base change"]
theorem baseChange_bijective_at (A : Hom f)
    (hA : A.baseChange_bijective) {i j : A.index} (h : i ≤ j) :
    Function.Bijective (A.baseChangeMap h) := sorry

/-- Every transition base-change map in a directed approximation is
injective. -/
@[stacks 00R0 "directed ring-hom approximation base change"]
def baseChange_injective (A : Hom f) : Prop :=
  ∀ {i j : A.index} (h : i ≤ j), Function.Injective (A.baseChangeMap h)

/-- Read the injectivity of one transition base-change map. -/
@[stacks 00R0 "directed ring-hom approximation base change"]
theorem baseChange_injective_at (A : Hom f)
    (hA : A.baseChange_injective) {i j : A.index} (h : i ≤ j) :
    Function.Injective (A.baseChangeMap h) := sorry

/-- A bijective transition base-change property supplies surjectivity. -/
@[stacks 00R0 "directed ring-hom approximation base change"]
theorem baseChange_surjective_of_bijective (A : Hom f)
    (hA : A.baseChange_bijective) : A.baseChange_surjective := sorry

/-- A bijective transition base-change property supplies injectivity. -/
@[stacks 00R0 "directed ring-hom approximation base change"]
theorem baseChange_injective_of_bijective (A : Hom f)
    (hA : A.baseChange_bijective) :
    A.baseChange_injective := sorry

/-- The base-change map at a comparable pair of stages, packaged as a ring
equivalence from an approximation with bijective base change. -/
@[stacks 00R0 "directed ring-hom approximation base change"]
noncomputable def baseChangeEquiv (A : Hom f)
    (h_bijective : A.baseChange_bijective) {i j : A.index} (h : i ≤ j) :
    A.baseChange h ≃+* A.target j :=
  RingEquiv.ofBijective (A.baseChangeMap h) (h_bijective h)

/-- The forward ring homomorphism of `baseChangeEquiv` is the canonical map. -/
@[simp, stacks 00R0 "directed ring-hom approximation base change"]
theorem baseChangeEquiv_hom (A : Hom f)
    (h_bijective : A.baseChange_bijective) {i j : A.index} (h : i ≤ j) :
    (A.baseChangeEquiv h_bijective h).toRingHom = A.baseChangeMap h := sorry

/-- The stage base-change equivalence evaluates on a pure tensor. -/
@[simp, stacks 00R0 "directed ring-hom approximation base change"]
theorem baseChangeEquiv_tmul (A : Hom f)
    (h_bijective : A.baseChange_bijective) {i j : A.index} (h : i ≤ j)
    (x : A.target i) (y : A.source j) :
    let _ : Algebra (A.source i) (A.target i) := (A.map i).toAlgebra
    let _ : Algebra (A.source i) (A.source j) := (A.sourceMap i j h).toAlgebra
    let _ : Algebra (A.source j) (A.target j) := (A.map j).toAlgebra
    let _ : Algebra (A.source i) (A.target j) :=
      ((A.map j).comp (A.sourceMap i j h)).toAlgebra
    let _ : IsScalarTower (A.source i) (A.source j) (A.target j) :=
      IsScalarTower.of_algebraMap_eq' rfl
    A.baseChangeEquiv h_bijective h (x ⊗ₜ[A.source i] y) =
      A.targetMap i j h x * A.map j y := sorry

/-- The stage base-change equivalence sends the canonical left generator to the
later stage map. -/
@[simp, stacks 00R0 "directed ring-hom approximation base change"]
theorem baseChangeEquiv_one_tmul (A : Hom f)
    (h_bijective : A.baseChange_bijective) {i j : A.index} (h : i ≤ j)
    (y : A.source j) :
    let _ : Algebra (A.source i) (A.target i) := (A.map i).toAlgebra
    let _ : Algebra (A.source i) (A.source j) := (A.sourceMap i j h).toAlgebra
    let _ : Algebra (A.source j) (A.target j) := (A.map j).toAlgebra
    let _ : Algebra (A.source i) (A.target j) :=
      ((A.map j).comp (A.sourceMap i j h)).toAlgebra
    let _ : IsScalarTower (A.source i) (A.source j) (A.target j) :=
      IsScalarTower.of_algebraMap_eq' rfl
    A.baseChangeEquiv h_bijective h (1 ⊗ₜ[A.source i] y) = A.map j y := sorry

/-- The source-oriented form of the stage base-change map.  The standard
`baseChangeMap` has domain `target i ⊗[source i] source j`; this bridge uses
the canonical tensor commutation equivalence to expose the equivalent
`source j ⊗[source i] target i` orientation used in many descent statements. -/
@[stacks 00R0 "directed ring-hom approximation base change"]
noncomputable def baseChangeCommMap (A : Hom f) {i j : A.index} (h : i ≤ j) :
    let _ : Algebra (A.source i) (A.target i) := (A.map i).toAlgebra
    let _ : Algebra (A.source i) (A.source j) := (A.sourceMap i j h).toAlgebra
    A.source j ⊗[A.source i] A.target i →+* A.target j :=
  let _ : Algebra (A.source i) (A.target i) := (A.map i).toAlgebra
  let _ : Algebra (A.source i) (A.source j) := (A.sourceMap i j h).toAlgebra
  (A.baseChangeMap h).comp
    (Algebra.TensorProduct.comm (A.source i) (A.source j) (A.target i)).toRingEquiv.toRingHom

/-- On a pure tensor, the source-oriented bridge applies the later source map
to the left factor and the target transition to the right factor. -/
@[simp, stacks 00R0 "directed ring-hom approximation base change"]
theorem baseChangeCommMap_tmul (A : Hom f) {i j : A.index} (h : i ≤ j)
    (x : A.source j) (y : A.target i) :
    let _ : Algebra (A.source i) (A.target i) := (A.map i).toAlgebra
    let _ : Algebra (A.source i) (A.source j) := (A.sourceMap i j h).toAlgebra
    let _ : Algebra (A.source j) (A.target j) := (A.map j).toAlgebra
    let _ : Algebra (A.source i) (A.target j) :=
      ((A.map j).comp (A.sourceMap i j h)).toAlgebra
    let _ : IsScalarTower (A.source i) (A.source j) (A.target j) :=
      IsScalarTower.of_algebraMap_eq' rfl
    A.baseChangeCommMap h (x ⊗ₜ[A.source i] y) =
      A.targetMap i j h y * A.map j x := sorry

/-- The source-oriented base-change equivalence obtained from a bijective
stage comparison. -/
@[stacks 00R0 "directed ring-hom approximation base change"]
noncomputable def baseChangeCommEquiv (A : Hom f)
    (h_bijective : A.baseChange_bijective) {i j : A.index} (h : i ≤ j) :
    let _ : Algebra (A.source i) (A.target i) := (A.map i).toAlgebra
    let _ : Algebra (A.source i) (A.source j) := (A.sourceMap i j h).toAlgebra
    A.source j ⊗[A.source i] A.target i ≃+* A.target j :=
  let _ : Algebra (A.source i) (A.target i) := (A.map i).toAlgebra
  let _ : Algebra (A.source i) (A.source j) := (A.sourceMap i j h).toAlgebra
  (Algebra.TensorProduct.comm (A.source i) (A.source j) (A.target i)).toRingEquiv.trans
    (A.baseChangeEquiv h_bijective h)

end Ring.DirectLimit.Algebra.Approximation.Hom
