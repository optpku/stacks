/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.FiberedCategory.HomLift
public import Mathlib.CategoryTheory.Limits.HasLimits
public import ReasLib.Algebra.Category.CommRingCat.InverseSystem

/-!
# Formal systems of objects over affine inverse limits

A formal object system records a sequential inverse system of affine schemes
over a fixed base together with compatible objects over its stages.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u v w

namespace AlgebraicGeometry

variable {S : Scheme.{u}} {C : Type v} [Category.{w} C]

/-- A sequential system of objects over spectra of algebras relative to an affine
open of a scheme. -/
structure FormalObjectSystem (p : C ⥤ Over S) where
  /-- Coefficient ring of the affine open. -/
  coeffRing : CommRingCat.{u}
  /-- The affine open immersion into the base scheme. -/
  openImmersion : Spec coeffRing ⟶ S
  /-- The structure morphism is an open immersion. -/
  isOpenImmersion : IsOpenImmersion openImmersion
  /-- Sequential inverse system of commutative rings. -/
  ringSystem : SequentialInverseSystem CommRingCat.{u}
  /-- A chosen limiting cone for the ring system. -/
  limitCone : LimitCone ringSystem
  /-- Structure morphisms exhibiting each stage as an algebra over the coefficient ring. -/
  algebra : ∀ n, coeffRing ⟶ ringSystem.family n
  /-- Compatibility of the stage algebra structures with successor maps. -/
  algebra_step : ∀ n, algebra (n + 1) ≫ ringSystem.stepMap n = algebra n
  /-- Surjectivity of the successor transition maps. -/
  ringMapsSurjective : ringSystem.Surjective
  /-- Local nilpotence of the kernels of the successor transition maps. -/
  kernelsLocallyNilpotent : ringSystem.KernelLocallyNilpotent
  /-- Structure morphism exhibiting the limit ring as an algebra over the coefficient ring. -/
  limitAlgebra : coeffRing ⟶ limitCone.cone.pt
  /-- Compatibility of the limit algebra with every cone leg. -/
  algebra_limit_π : ∀ n, limitAlgebra ≫ limitCone.cone.stageMap n = algebra n
  /-- Objects of the total category over the stages. -/
  objects : ℕ → C
  /-- Successor morphisms of the object system. -/
  step : ∀ n, objects n ⟶ objects (n + 1)
  /-- The object at each stage lies over the corresponding spectrum. -/
  over_obj : ∀ n, p.obj (objects n) =
    Over.mk (Spec.map (algebra n) ≫ openImmersion)
  /-- The successor spectrum maps are compatible with the structure maps to the base. -/
  step_comp : ∀ n,
    Spec.map (ringSystem.stepMap n) ≫
        (Spec.map (algebra (n + 1)) ≫ openImmersion) =
      Spec.map (algebra n) ≫ openImmersion
  /-- The successor morphisms lie over the successor spectrum maps. -/
  over_step : ∀ n,
    p.IsHomLift
      (Over.homMk (Spec.map (ringSystem.stepMap n)) (step_comp n) :
        Over.mk (Spec.map (algebra n) ≫ openImmersion) ⟶
          Over.mk (Spec.map (algebra (n + 1)) ≫ openImmersion))
      (step n)

namespace FormalObjectSystem

variable {p : C ⥤ Over S} (ξ : FormalObjectSystem p)

/-- Construct a formal object system from its constituent coefficient, diagram,
object, and compatibility data. -/
def ofFields
    (coeffRing : CommRingCat.{u})
    (openImmersion : Spec coeffRing ⟶ S)
    (isOpenImmersion : IsOpenImmersion openImmersion)
    (ringSystem : SequentialInverseSystem CommRingCat.{u})
    (limitCone : LimitCone ringSystem)
    (algebra : ∀ n, coeffRing ⟶ ringSystem.family n)
    (algebra_step : ∀ n, algebra (n + 1) ≫ ringSystem.stepMap n = algebra n)
    (ringMapsSurjective : ringSystem.Surjective)
    (kernelsLocallyNilpotent : ringSystem.KernelLocallyNilpotent)
    (limitAlgebra : coeffRing ⟶ limitCone.cone.pt)
    (algebra_limit_π : ∀ n, limitAlgebra ≫ limitCone.cone.stageMap n = algebra n)
    (objects : ℕ → C)
    (step : ∀ n, objects n ⟶ objects (n + 1))
    (over_obj : ∀ n, p.obj (objects n) =
      Over.mk (Spec.map (algebra n) ≫ openImmersion))
    (step_comp : ∀ n,
      Spec.map (ringSystem.stepMap n) ≫
          (Spec.map (algebra (n + 1)) ≫ openImmersion) =
        Spec.map (algebra n) ≫ openImmersion)
    (over_step : ∀ n,
      p.IsHomLift
        (Over.homMk (Spec.map (ringSystem.stepMap n)) (step_comp n) :
          Over.mk (Spec.map (algebra n) ≫ openImmersion) ⟶
            Over.mk (Spec.map (algebra (n + 1)) ≫ openImmersion))
        (step n)) :
    FormalObjectSystem p :=
  { coeffRing
    openImmersion
    isOpenImmersion
    ringSystem
    limitCone
    algebra
    algebra_step
    ringMapsSurjective
    kernelsLocallyNilpotent
    limitAlgebra
    algebra_limit_π
    objects
    step
    over_obj
    step_comp
    over_step }

/-- The spectrum of the ring at stage `n`. -/
def stageSpec (n : ℕ) : Scheme.{u} :=
  Spec (ξ.ringSystem.family n)

/-- The spectrum of the limiting ring. -/
def limitSpec : Scheme.{u} :=
  Spec ξ.limitCone.cone.pt

/-- The structure morphism from the stage spectrum to the base scheme. -/
def stageToS (n : ℕ) : ξ.stageSpec n ⟶ S :=
  Spec.map (ξ.algebra n) ≫ ξ.openImmersion

/-- The structure morphism from the limiting spectrum to the base scheme. -/
def limitToS : ξ.limitSpec ⟶ S :=
  Spec.map ξ.limitAlgebra ≫ ξ.openImmersion

/-- The stage spectrum viewed as an object over the base scheme. -/
def stageOver (n : ℕ) : Over S :=
  Over.mk (ξ.stageToS n)

/-- The limiting spectrum viewed as an object over the base scheme. -/
def limitOver : Over S :=
  Over.mk ξ.limitToS

/-- The comparison map from a stage spectrum to the limiting spectrum. -/
def stageToLimitScheme (n : ℕ) : ξ.stageSpec n ⟶ ξ.limitSpec :=
  Spec.map (ξ.limitCone.cone.stageMap n)

/-- The comparison map from each stage spectrum lies over the base scheme. -/
theorem stageToLimit_comp (n : ℕ) :
    ξ.stageToLimitScheme n ≫ ξ.limitToS = ξ.stageToS n := sorry

/-- A formal object system is effective when one object over the limiting
spectrum realizes all stages compatibly. -/
def IsEffective : Prop :=
  ∃ (x : C) (_ : p.obj x = ξ.limitOver) (φ : ∀ n, ξ.objects n ⟶ x),
    (∀ n, p.IsHomLift
        (Over.homMk (ξ.stageToLimitScheme n) (ξ.stageToLimit_comp n) :
          ξ.stageOver n ⟶ ξ.limitOver)
        (φ n)) ∧
      (∀ n, ξ.step n ≫ φ (n + 1) = φ n)

/-- Effectiveness is characterized by the existence of a compatible realization
over the limiting spectrum. -/
theorem isEffective_iff :
    ξ.IsEffective ↔
      ∃ (x : C) (_ : p.obj x = ξ.limitOver) (φ : ∀ n, ξ.objects n ⟶ x),
        (∀ n, p.IsHomLift
            (Over.homMk (ξ.stageToLimitScheme n) (ξ.stageToLimit_comp n) :
              ξ.stageOver n ⟶ ξ.limitOver)
            (φ n)) ∧
          (∀ n, ξ.step n ≫ φ (n + 1) = φ n) := sorry

/-- An effective formal object system has a compatible realization over the
limiting spectrum. -/
theorem exists_object (h : ξ.IsEffective) :
    ∃ (x : C) (_ : p.obj x = ξ.limitOver) (φ : ∀ n, ξ.objects n ⟶ x),
      (∀ n, p.IsHomLift
          (Over.homMk (ξ.stageToLimitScheme n) (ξ.stageToLimit_comp n) :
            ξ.stageOver n ⟶ ξ.limitOver)
          (φ n)) ∧
        (∀ n, ξ.step n ≫ φ (n + 1) = φ n) := sorry

end FormalObjectSystem

end AlgebraicGeometry
