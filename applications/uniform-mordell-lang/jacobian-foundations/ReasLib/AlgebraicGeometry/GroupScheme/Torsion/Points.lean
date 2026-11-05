/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

The pullback comparison is adapted from NYLL, revision
8c1b16d10afaca09e0dc72753c6575e230d31a55,
Nyll/AbelianVarieties/Tate/FullTateModule.lean, lines 42--94.
The kernel construction also follows its GroupLaw/Kernel.lean, which retains
Copyright 2026 Anthropic, PBC; see the accompanying NOTICE.
This adaptation changes the canonical carrier to Mathlib group objects.

Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Kernel source reference:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GoodReductionJacobian_RelativeGroupLawKernel.lean
Upstream NOTICE and earlier per-file attributions are preserved by the
accompanying NYLL NOTICE and its FLT attribution links.
-/
module

public import ReasLib.AlgebraicGeometry.GroupObject.Points
public import ReasLib.CategoryTheory.Monoidal.Grp.MulBy

/-!
# Torsion points and the actual multiplication kernel

For a group object `G : Over S`, the morphism `[n]` is the `n`th power of the
identity in Mathlib's group of `G`-valued points. Its scheme theoretic fibre at
the identity represents the points killed by `n`, naturally in every test
scheme. This construction works over any base and for `n = 0` as well.

Commutativity is needed to call `[n]` a group homomorphism or its pointwise
kernel a subgroup, but is not needed for the representable fibre comparison.
Finiteness, flatness, etaleness, and surjectivity require separate theorems.
-/

@[expose] public section

-- Keep elaboration compatible with the Mathlib pullback presentation on both supported pins.
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.GroupObject

variable {S : Scheme.{u}} (G : Over S) [GrpObj G]

/-- A thin name for ReasLib's canonical multiplication-by-`n` morphism over the base. -/
abbrev multiplyBy (n : ℕ) : G ⟶ G := GrpObj.mulBy G n

@[simp]
theorem comp_multiplyBy {T : Over S} (x : T ⟶ G) (n : ℕ) :
    x ≫ multiplyBy G n = x ^ n := by
  simp [multiplyBy, MonObj.comp_pow]

/-- The identity section over the base. -/
def identitySection : Over.mk (𝟙 S) ⟶ G := 1

@[simp]
theorem comp_identitySection (T : Over S) :
    (Over.homMk T.hom : T ⟶ Over.mk (𝟙 S)) ≫ identitySection G = 1 :=
  MonObj.comp_one _

/-- The scheme theoretic kernel, defined as the fibre of `[n]` at the identity section. -/
abbrev multiplicationKernel (n : ℕ) : Over S :=
  Over.mk (pullback.snd (multiplyBy G n).left (identitySection G).left)

/-- The kernel's actual inclusion into `G`, as a morphism over `S`. -/
def kernelInclusion (n : ℕ) : multiplicationKernel G n ⟶ G :=
  Over.homMk (pullback.fst (multiplyBy G n).left (identitySection G).left) (by
    change pullback.fst (multiplyBy G n).left (identitySection G).left ≫ G.hom =
      pullback.snd (multiplyBy G n).left (identitySection G).left
    rw [← Over.w (multiplyBy G n), ← Category.assoc, pullback.condition,
      Category.assoc, Over.w (identitySection G)]
    exact Category.comp_id _)

/-- Points killed by `n` in the actual functor-of-points group. -/
abbrev TorsionPoints (T : Over S) (n : ℕ) := {x : T ⟶ G // x ^ n = 1}

/-- Torsion points over any test scheme are points of the actual multiplication kernel. -/
def torsionSubsetEquivSchemeKerPoints (T : Over S) (n : ℕ) :
    TorsionPoints G T n ≃ (T ⟶ multiplicationKernel G n) where
  toFun x := Over.homMk (pullback.lift x.1.left T.hom (by
    have h := congrArg (fun y : T ⟶ G => y.left) (comp_multiplyBy G x.1 n)
    rw [x.2] at h
    have he := congrArg (fun y : T ⟶ G => y.left) (comp_identitySection G T)
    exact h.trans he.symm)) (pullback.lift_snd _ _ _)
  invFun z := ⟨z ≫ kernelInclusion G n, by
    rw [← comp_multiplyBy]
    apply Over.OverMorphism.ext
    change (z.left ≫ pullback.fst _ _) ≫ (multiplyBy G n).left =
      (1 : T ⟶ G).left
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    change (z.left ≫ (multiplicationKernel G n).hom) ≫
      (identitySection G).left = (1 : T ⟶ G).left
    rw [Over.w z]
    exact congrArg (fun y : T ⟶ G => y.left) (comp_identitySection G T)⟩
  left_inv x := by
    apply Subtype.ext
    apply Over.OverMorphism.ext
    exact pullback.lift_fst _ _ _
  right_inv z := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · exact (pullback.lift_snd _ _ _).trans (Over.w z).symm

/-- The comparison preserves the underlying point of the group scheme. -/
@[simp]
theorem torsionSubsetEquivSchemeKerPoints_comp_inclusion (T : Over S) (n : ℕ)
    (x : TorsionPoints G T n) :
    torsionSubsetEquivSchemeKerPoints G T n x ≫ kernelInclusion G n = x.1 := by
  apply Over.OverMorphism.ext
  exact pullback.lift_fst _ _ _

/-- The kernel comparison on underlying scheme morphisms. -/
@[simp]
theorem torsionSubsetEquivSchemeKerPoints_comp_fst (T : Over S) (n : ℕ)
    (x : TorsionPoints G T n) :
    (torsionSubsetEquivSchemeKerPoints G T n x).left ≫
      pullback.fst (multiplyBy G n).left (identitySection G).left = x.1.left :=
  pullback.lift_fst _ _ _

/-- Restriction of torsion points is precomposition, including at `n = 0`. -/
def restrictTorsionPoints {T T' : Over S} (a : T' ⟶ T) (n : ℕ)
    (x : TorsionPoints G T n) : TorsionPoints G T' n :=
  ⟨a ≫ x.1, by rw [← MonObj.comp_pow, x.2, MonObj.comp_one]⟩

/-- Naturality in the test scheme, hence also compatibility with extension of coefficients. -/
theorem torsionSubsetEquivSchemeKerPoints_natural {T T' : Over S} (a : T' ⟶ T)
    (n : ℕ) (x : TorsionPoints G T n) :
    torsionSubsetEquivSchemeKerPoints G T' n (restrictTorsionPoints G a n x) =
      a ≫ torsionSubsetEquivSchemeKerPoints G T n x := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp [Category.assoc, restrictTorsionPoints]
  · exact (Over.w _).trans (Over.w _).symm

end AlgebraicGeometry.Scheme.GroupObject
