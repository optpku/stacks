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
  rfl

/-- The successor morphism `Spec(R_n) ⟶ Spec(R_{n+1})` in `Over S`. -/
def stageStep (n : ℕ) : ξ.stageOver n ⟶ ξ.stageOver (n + 1) :=
  Over.homMk (Spec.map (ξ.ringSystem.stepMap n)) (ξ.step_comp n)

/-- The underlying scheme morphism of `stageStep n` is `Spec.map` of the successor
ring transition. -/
theorem stageStep_left (n : ℕ) :
    (ξ.stageStep n).left = Spec.map (ξ.ringSystem.stepMap n) :=
  rfl

/-- Stage comparison factors through the successor: `stageToLimitOver n` equals
`stageStep n ≫ stageToLimitOver (n + 1)`. -/
theorem stageToLimitOver_succ (n : ℕ) :
    ξ.stageToLimitOver n = ξ.stageStep n ≫ ξ.stageToLimitOver (n + 1) := by
  apply Over.OverMorphism.ext
  have h : ξ.limitCone.cone.stageMap (n + 1) ≫ ξ.ringSystem.stepMap n =
      ξ.limitCone.cone.stageMap n :=
    ξ.limitCone.cone.w (homOfLE (Nat.le_add_right n 1)).op
  change Spec.map (ξ.limitCone.cone.stageMap n) =
    Spec.map (ξ.ringSystem.stepMap n) ≫
      Spec.map (ξ.limitCone.cone.stageMap (n + 1))
  simpa only [Spec.map_comp] using
    congrArg (fun f : ξ.limitCone.cone.pt ⟶ ξ.ringSystem.family n ↦ Spec.map f) h.symm

section RestrictionLemmas

variable {B E : Type*} [Category* B] [Category* E] {q : E ⥤ B} [q.IsFibered]

@[reassoc]
private theorem limitComparison_restrictHom_fac {U V : B} {x y : q.Fiber U}
    (φ : x ⟶ y) (f : V ⟶ U) :
    (restrictHom φ f).1 ≫ Functor.IsPreFibered.pullbackMap y.property f =
      Functor.IsPreFibered.pullbackMap x.property f ≫ φ.1 := by
  haveI := φ.property
  exact Functor.IsCartesian.fac q f (Functor.IsPreFibered.pullbackMap y.property f)
    (Functor.IsPreFibered.pullbackMap x.property f ≫ φ.1)

private theorem limitComparison_restrictHom_id {U V : B} (x : q.Fiber U)
    (f : V ⟶ U) : restrictHom (𝟙 x) f = 𝟙 (restrictObj x f) := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  change Functor.IsCartesian.map q f (Functor.IsPreFibered.pullbackMap x.property f)
    (Functor.IsPreFibered.pullbackMap x.property f ≫ 𝟙 x.1) = 𝟙 _
  simp

set_option backward.isDefEq.respectTransparency false in
private theorem limitComparison_restrictHom_comp {U V : B} {x y z : q.Fiber U}
    (φ : x ⟶ y) (ψ : y ⟶ z) (f : V ⟶ U) :
    restrictHom (φ ≫ ψ) f = restrictHom φ f ≫ restrictHom ψ f := by
  apply Subtype.ext
  change (restrictHom (φ ≫ ψ) f).1 = (restrictHom φ f).1 ≫ (restrictHom ψ f).1
  haveI := (restrictHom (φ ≫ ψ) f).property
  haveI := (restrictHom φ f).property
  haveI := (restrictHom ψ f).property
  haveI := IsHomLift.comp_of_lift_id q V
    (restrictHom φ f).1 (restrictHom ψ f).1
  apply Functor.IsCartesian.ext q f (Functor.IsPreFibered.pullbackMap z.property f)
  simp only [Category.assoc, limitComparison_restrictHom_fac,
    limitComparison_restrictHom_fac_assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem limitComparison_restrictObj_comp_hom_fac {U V W : B} (x : q.Fiber U)
    (f : V ⟶ U) (g : W ⟶ V) :
    (restrictObj_comp x f g).hom.1 ≫ Functor.IsPreFibered.pullbackMap x.property (g ≫ f) =
      Functor.IsPreFibered.pullbackMap (restrictObj x f).property g ≫
        Functor.IsPreFibered.pullbackMap x.property f := by
  haveI := IsHomLift.comp q g f
    (Functor.IsPreFibered.pullbackMap (restrictObj x f).property g)
    (Functor.IsPreFibered.pullbackMap x.property f)
  exact Functor.IsCartesian.fac q (g ≫ f)
    (Functor.IsPreFibered.pullbackMap x.property (g ≫ f))
    (Functor.IsPreFibered.pullbackMap (restrictObj x f).property g ≫
      Functor.IsPreFibered.pullbackMap x.property f)

set_option backward.isDefEq.respectTransparency false in
private theorem limitComparison_restrictHom_comp_naturality {U V W : B}
    {x y : q.Fiber U} (φ : x ⟶ y) (f : V ⟶ U) (g : W ⟶ V) :
    restrictHom (restrictHom φ f) g ≫ (restrictObj_comp y f g).hom =
      (restrictObj_comp x f g).hom ≫ restrictHom φ (g ≫ f) := by
  apply Subtype.ext
  change (restrictHom (restrictHom φ f) g).1 ≫ (restrictObj_comp y f g).hom.1 =
    (restrictObj_comp x f g).hom.1 ≫ (restrictHom φ (g ≫ f)).1
  haveI := (restrictHom (restrictHom φ f) g).property
  haveI := (restrictObj_comp y f g).hom.property
  haveI := (restrictObj_comp x f g).hom.property
  haveI := (restrictHom φ (g ≫ f)).property
  haveI := IsHomLift.comp_of_lift_id q W
    (restrictHom (restrictHom φ f) g).1 (restrictObj_comp y f g).hom.1
  haveI := IsHomLift.comp_of_lift_id q W
    (restrictObj_comp x f g).hom.1 (restrictHom φ (g ≫ f)).1
  apply Functor.IsCartesian.ext q (g ≫ f)
    (Functor.IsPreFibered.pullbackMap y.property (g ≫ f))
  simp only [Category.assoc, limitComparison_restrictObj_comp_hom_fac,
    limitComparison_restrictObj_comp_hom_fac_assoc, limitComparison_restrictHom_fac,
    limitComparison_restrictHom_fac_assoc]

private theorem limitComparison_restrictHom_naturality {U V W : B} {x y : q.Fiber U}
    (φ : x ⟶ y) (f : V ⟶ U) (g : W ⟶ V) {h : W ⟶ U} (he : g ≫ f = h) :
    restrictHom (restrictHom φ f) g =
      (restrictObj_comp x f g ≪≫ restrictObj_eq x he).hom ≫ restrictHom φ h ≫
        (restrictObj_comp y f g ≪≫ restrictObj_eq y he).inv := by
  subst h
  simp only [restrictObj_eq, eqToIso_refl, Iso.trans_refl]
  calc
    restrictHom (restrictHom φ f) g =
        (restrictHom (restrictHom φ f) g ≫ (restrictObj_comp y f g).hom) ≫
          (restrictObj_comp y f g).inv := by simp
    _ = ((restrictObj_comp x f g).hom ≫ restrictHom φ (g ≫ f)) ≫
        (restrictObj_comp y f g).inv := by
      rw [limitComparison_restrictHom_comp_naturality]
    _ = _ := Category.assoc _ _ _

end RestrictionLemmas

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
  naturality := by
    intro n
    rw [limitComparison_restrictHom_id]
    simp

/-- Composition of compatible families is composition at every stage. -/
def comp {x y z : p.Fiber ξ.limitOver}
    (φ : CompatibleStageHom ξ x y) (ψ : CompatibleStageHom ξ y z) :
    CompatibleStageHom ξ x z where
  app n := φ.app n ≫ ψ.app n
  naturality := by
    intro n
    rw [limitComparison_restrictHom_comp]
    rw [φ.naturality n, ψ.naturality n]
    simp

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
  naturality := by
    intro n
    exact limitComparison_restrictHom_naturality φ (ξ.stageToLimitOver (n + 1))
      (ξ.stageStep n) (ξ.stageToLimitOver_succ n).symm

/-- The `n`th component of `compatibleStageHom φ` is restriction along
`stageToLimitOver n`. -/
theorem compatibleStageHom_app {x y : p.Fiber ξ.limitOver} (φ : x ⟶ y) (n : ℕ) :
    (ξ.compatibleStageHom φ).app n = restrictHom φ (ξ.stageToLimitOver n) :=
  rfl

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
            ∃! φ : x ⟶ y, ξ.compatibleStageHom φ = fam := by
  constructor
  · intro h x y
    obtain ⟨hinj, hsurj⟩ := h x y
    refine ⟨hinj, ?_⟩
    intro fam
    obtain ⟨φ, hφ⟩ := hsurj fam
    exact ⟨φ, hφ, fun ψ hψ ↦ hinj (hψ.trans hφ.symm)⟩
  · intro h x y
    obtain ⟨hinj, hsurj⟩ := h x y
    exact ⟨hinj, fun fam ↦ (hsurj fam).exists⟩

end AlgebraicGeometry.FormalObjectSystem
