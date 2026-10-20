/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Sites.Limits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.CommRingHom
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation

/-!
# Invariant functions of a pre-relation

For an invariant morphism of algebraic spaces, the invariant-function sheaf is the
equalizer of the two direct-image structure maps on the target's small étale site.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

namespace PreRelation

/-- The map `φ_* s^♯ : φ_* 𝒪_U ⟶ (φ ∘ s)_* 𝒪_R` on `X_étale`. -/
def sourceSharpPushforward {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) :
    (ringPushforward φ.left).obj (structureSheaf U.left) ⟶
      (ringPushforward (P.s.left ≫ φ.left)).obj (structureSheaf P.left.left) :=
  (ringPushforward φ.left).map (structureSheafMap P.s.left) ≫
    (sheafCompose (smallEtaleTopology X.left) (forget₂ CommRingCat.{u} RingCat.{u})).map
      ((commRingPushforwardComp P.s.left φ.left).hom.app
        (commStructureSheaf P.left.left))

/-- `sourceSharpPushforward` is pushforward of `s^♯` followed by the associator. -/
theorem sourceSharpPushforward_eq {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) :
    P.sourceSharpPushforward φ =
      (ringPushforward φ.left).map (structureSheafMap P.s.left) ≫
        (sheafCompose (smallEtaleTopology X.left) (forget₂ CommRingCat.{u} RingCat.{u})).map
          ((commRingPushforwardComp P.s.left φ.left).hom.app
            (commStructureSheaf P.left.left)) :=
  rfl

/-- Transport of `(φ ∘ t)_* 𝒪_R` to `(φ ∘ s)_* 𝒪_R` along `R`-invariance. -/
def targetDirectImageIso {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) (h : P.t ≫ φ = P.s ≫ φ) :
    (ringPushforward (P.t.left ≫ φ.left)).obj (structureSheaf P.left.left) ≅
      (ringPushforward (P.s.left ≫ φ.left)).obj (structureSheaf P.left.left) :=
  eqToIso (congrArg (fun g ↦ (ringPushforward g).obj (structureSheaf P.left.left))
    (congrArg (fun ψ : P.left ⟶ X ↦ ψ.left) h))

/-- `targetDirectImageIso` is the identity transport along the underlying equality
`P.t.left ≫ φ.left = P.s.left ≫ φ.left`. -/
theorem targetDirectImageIso_eq {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) (h : P.t ≫ φ = P.s ≫ φ) :
    P.targetDirectImageIso φ h =
      eqToIso (congrArg (fun g ↦ (ringPushforward g).obj (structureSheaf P.left.left))
        (congrArg (fun ψ : P.left ⟶ X ↦ ψ.left) h)) :=
  rfl

/-- The map `φ_* t^♯ : φ_* 𝒪_U ⟶ (φ ∘ s)_* 𝒪_R` on `X_étale`, after transporting the
target along `R`-invariance. -/
def targetSharpPushforward {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) (h : P.t ≫ φ = P.s ≫ φ) :
    (ringPushforward φ.left).obj (structureSheaf U.left) ⟶
      (ringPushforward (P.s.left ≫ φ.left)).obj (structureSheaf P.left.left) :=
  (ringPushforward φ.left).map (structureSheafMap P.t.left) ≫
    (sheafCompose (smallEtaleTopology X.left) (forget₂ CommRingCat.{u} RingCat.{u})).map
      ((commRingPushforwardComp P.t.left φ.left).hom.app
        (commStructureSheaf P.left.left)) ≫ (P.targetDirectImageIso φ h).hom

/-- `targetSharpPushforward` is pushforward of `t^♯`, the associator, and invariance
transport. -/
theorem targetSharpPushforward_eq {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) (h : P.t ≫ φ = P.s ≫ φ) :
    P.targetSharpPushforward φ h =
      (ringPushforward φ.left).map (structureSheafMap P.t.left) ≫
        (sheafCompose (smallEtaleTopology X.left) (forget₂ CommRingCat.{u} RingCat.{u})).map
          ((commRingPushforwardComp P.t.left φ.left).hom.app
            (commStructureSheaf P.left.left)) ≫ (P.targetDirectImageIso φ h).hom :=
  rfl

/-- The sheaf of `R`-invariant functions `(φ_* 𝒪_U)^R` on `X_étale`, as the equalizer of
`φ_* s^♯` and `φ_* t^♯`. -/
def invariantFunctions {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) (h : P.t ≫ φ = P.s ≫ φ) :
    Sheaf (smallEtaleTopology X.left) RingCat.{u} :=
  equalizer (P.sourceSharpPushforward φ) (P.targetSharpPushforward φ h)

/-- `invariantFunctions` is the equalizer of `sourceSharpPushforward` and
`targetSharpPushforward`. -/
theorem invariantFunctions_eq {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) (h : P.t ≫ φ = P.s ≫ φ) :
    P.invariantFunctions φ h =
      equalizer (P.sourceSharpPushforward φ) (P.targetSharpPushforward φ h) :=
  rfl

/-- The inclusion `(φ_* 𝒪_U)^R ⟶ φ_* 𝒪_U` of the sheaf of `R`-invariant functions. -/
def invariantFunctionsι {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) (h : P.t ≫ φ = P.s ≫ φ) :
    P.invariantFunctions φ h ⟶ (ringPushforward φ.left).obj (structureSheaf U.left) :=
  equalizer.ι (P.sourceSharpPushforward φ) (P.targetSharpPushforward φ h)

/-- The equalizer inclusion equalizes `φ_* s^♯` and `φ_* t^♯`. -/
theorem invariantFunctionsι_equalizes {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) (h : P.t ≫ φ = P.s ≫ φ) :
    P.invariantFunctionsι φ h ≫ P.sourceSharpPushforward φ =
      P.invariantFunctionsι φ h ≫ P.targetSharpPushforward φ h :=
  equalizer.condition (P.sourceSharpPushforward φ) (P.targetSharpPushforward φ h)

/-- The structure map `φ^♯` equalizes `φ_* s^♯` and `φ_* t^♯`. -/
theorem structureSheafMap_equalizes {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) (h : P.t ≫ φ = P.s ≫ φ) :
    structureSheafMap φ.left ≫ P.sourceSharpPushforward φ =
      structureSheafMap φ.left ≫ P.targetSharpPushforward φ h :=
  sorry

/-- The natural map `𝒪_X ⟶ (φ_* 𝒪_U)^R` factoring `φ^♯` through the equalizer of
`R`-invariant functions. -/
def structureSheafToInvariantFunctions {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) (h : P.t ≫ φ = P.s ≫ φ) :
    structureSheaf X.left ⟶ P.invariantFunctions φ h :=
  equalizer.lift (structureSheafMap φ.left) (P.structureSheafMap_equalizes φ h)

/-- The natural map composed with the equalizer inclusion recovers `φ^♯`. -/
theorem structureSheafToInvariantFunctions_comp_ι {B : AlgebraicSpace S}
    {U X : Over B} (P : PreRelation U) (φ : U ⟶ X) (h : P.t ≫ φ = P.s ≫ φ) :
    P.structureSheafToInvariantFunctions φ h ≫ P.invariantFunctionsι φ h =
      structureSheafMap φ.left :=
  equalizer.lift_ι (structureSheafMap φ.left) (P.structureSheafMap_equalizes φ h)

/-- The functions on `X` are the `R`-invariant functions on `U` when
`𝒪_X ⟶ (φ_* 𝒪_U)^R` is an isomorphism. -/
def HasInvariantFunctions {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) (h : P.t ≫ φ = P.s ≫ φ) : Prop :=
  IsIso (P.structureSheafToInvariantFunctions φ h)

/-- `HasInvariantFunctions` is precisely the assertion that the natural map is an
isomorphism. -/
theorem hasInvariantFunctions_iff {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) (h : P.t ≫ φ = P.s ≫ φ) :
    P.HasInvariantFunctions φ h ↔ IsIso (P.structureSheafToInvariantFunctions φ h) :=
  Iff.rfl

end PreRelation

end AlgebraicGeometry.AlgebraicSpace
