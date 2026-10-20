/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalObjectSystem
public import ReasLib.CategoryTheory.Fibered.Fiber.Restriction

/-!
# Hom comparisons for formal object systems

Restriction from the limiting spectrum gives compatible families of stage
morphisms. These families have explicit identity and composition operations.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Functor.Fiber

noncomputable section

universe u v w

namespace AlgebraicGeometry.FormalObjectSystem

variable {S : Scheme.{u}} {C : Type v} [Category.{w} C] {p : C ⥤ Over S}
variable (ξ : FormalObjectSystem p)

/-- The comparison morphism `Spec(R_n) ⟶ Spec(lim R_n)` in `Over S`. -/
def stageToLimitOver (n : ℕ) : ξ.stageOver n ⟶ ξ.limitOver :=
  Over.homMk (ξ.stageToLimitScheme n) (ξ.stageToLimit_comp n)

/-- The underlying scheme morphism of `stageToLimitOver n` is `stageToLimitScheme n`. -/
theorem stageToLimitOver_left (n : ℕ) :
    (ξ.stageToLimitOver n).left = ξ.stageToLimitScheme n :=
  sorry

/-- The successor morphism `Spec(R_n) ⟶ Spec(R_{n+1})` in `Over S`. -/
def stageStep (n : ℕ) : ξ.stageOver n ⟶ ξ.stageOver (n + 1) :=
  Over.homMk (Spec.map (ξ.ringSystem.stepMap n)) (ξ.step_comp n)

/-- The underlying scheme morphism of `stageStep n` is `Spec.map` of the successor
ring transition. -/
theorem stageStep_left (n : ℕ) :
    (ξ.stageStep n).left = Spec.map (ξ.ringSystem.stepMap n) :=
  sorry

/-- Stage comparison factors through the successor: `stageToLimitOver n` equals
`stageStep n ≫ stageToLimitOver (n + 1)`. -/
theorem stageToLimitOver_succ (n : ℕ) :
    ξ.stageToLimitOver n = ξ.stageStep n ≫ ξ.stageToLimitOver (n + 1) :=
  sorry

variable [p.IsFibered]

/-- A compatible family of fibre morphisms over the stages `Spec(R_n)`, the Hom-data
of an object of `lim_n X_{Spec(R_n)}`. -/
structure CompatibleStageHom (x y : p.Fiber ξ.limitOver) where
  /-- The fibre morphism over `Spec(R_n)`. -/
  app : ∀ n, restrictObj x (ξ.stageToLimitOver n) ⟶ restrictObj y (ξ.stageToLimitOver n)
  /-- Successive components are compatible under restriction along `stageStep n`. -/
  naturality : ∀ n,
    restrictHom (app (n + 1)) (ξ.stageStep n) =
      (restrictObj_comp x (ξ.stageToLimitOver (n + 1)) (ξ.stageStep n) ≪≫
          restrictObj_eq x (ξ.stageToLimitOver_succ n).symm).hom ≫
        app n ≫
          (restrictObj_comp y (ξ.stageToLimitOver (n + 1)) (ξ.stageStep n) ≪≫
              restrictObj_eq y (ξ.stageToLimitOver_succ n).symm).inv

namespace CompatibleStageHom

/-- The compatible family whose component at every stage is the identity. -/
def id (x : p.Fiber ξ.limitOver) : CompatibleStageHom ξ x x where
  app n := 𝟙 (restrictObj x (ξ.stageToLimitOver n))
  naturality := sorry

/-- Composition of compatible families is composition at every stage. -/
def comp {x y z : p.Fiber ξ.limitOver}
    (φ : CompatibleStageHom ξ x y) (ψ : CompatibleStageHom ξ y z) :
    CompatibleStageHom ξ x z where
  app n := φ.app n ≫ ψ.app n
  naturality := sorry

/-- Every component of the identity compatible family is the identity morphism. -/
theorem id_app (x : p.Fiber ξ.limitOver) (n : ℕ) :
    (id ξ x).app n = 𝟙 (restrictObj x (ξ.stageToLimitOver n)) :=
  rfl

/-- Every component of a composite compatible family is the composite of its components. -/
theorem comp_app {x y z : p.Fiber ξ.limitOver}
    (φ : CompatibleStageHom ξ x y) (ψ : CompatibleStageHom ξ y z) (n : ℕ) :
    (comp ξ φ ψ).app n = φ.app n ≫ ψ.app n :=
  rfl

end CompatibleStageHom

/-- Restriction of a fibre morphism over `Spec(lim R_n)` along every
`stageToLimitOver n`. -/
def compatibleStageHom {x y : p.Fiber ξ.limitOver} (φ : x ⟶ y) :
    CompatibleStageHom ξ x y where
  app n := restrictHom φ (ξ.stageToLimitOver n)
  naturality := sorry

/-- The `n`th component of `compatibleStageHom φ` is restriction along
`stageToLimitOver n`. -/
theorem compatibleStageHom_app {x y : p.Fiber ξ.limitOver} (φ : x ⟶ y) (n : ℕ) :
    (ξ.compatibleStageHom φ).app n = restrictHom φ (ξ.stageToLimitOver n) :=
  sorry

/-- The comparison `X_{Spec(lim R_n)} ⟶ lim_n X_{Spec(R_n)}` is fully faithful:
fibre morphisms over the limiting spectrum correspond bijectively to compatible
stage morphisms. -/
def IsLimitComparisonFullyFaithful : Prop :=
  ∀ (x y : p.Fiber ξ.limitOver),
    Function.Bijective (fun φ : x ⟶ y ↦ ξ.compatibleStageHom φ)

/-- Fully faithfulness of the limit-fibre comparison is injectivity of restriction
from the limit together with surjectivity onto compatible stage Hom-families. -/
theorem isLimitComparisonFullyFaithful_iff :
    ξ.IsLimitComparisonFullyFaithful ↔
      ∀ (x y : p.Fiber ξ.limitOver),
        Function.Injective (fun φ : x ⟶ y ↦ ξ.compatibleStageHom φ) ∧
          ∀ fam : CompatibleStageHom ξ x y,
            ∃! φ : x ⟶ y, ξ.compatibleStageHom φ = fam :=
  sorry

end AlgebraicGeometry.FormalObjectSystem
