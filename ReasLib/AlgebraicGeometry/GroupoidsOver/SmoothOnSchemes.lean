/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.SchemeBaseChange
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReasLib.CategoryTheory.Fibered.RelativelyRepresentable.BaseChange

/-!
# Smooth morphisms from schemes to categories fibred in groupoids

A morphism from a scheme slice is smooth on schemes when it is relatively
representable and every representing scheme base change has smooth projection.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids (overMap)
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/-- A 1-morphism from a scheme slice to a category fibred in groupoids over
`Over B` (for example `S ⟶ ℳ_{1,1}`) is smooth when it is relatively
representable and, for every test morphism `S' ⟶ X`, every scheme representing
the 2-fibre product has smooth projection `S ×_X S' ⟶ S'`. -/
class SmoothOnSchemes {B : Scheme.{u}} {X : GroupoidsOver B} {S : Over B}
    (f : GroupoidsOver.slice S ⟶ X) : Prop where
  /-- The 1-morphism is relatively representable. -/
  representable : FiberedCategoryOver.Groupoids.relativelyRepresentable f
  /-- Every representing projection of a scheme-theoretic fibre product is a
  smooth morphism of schemes. -/
  of_represents : ∀ ⦃S' : Over B⦄ (g : GroupoidsOver.slice S' ⟶ X)
    (W : Over B) (π : W ⟶ S'),
    RepresentsSchemeBaseChange f g W π → AlgebraicGeometry.Smooth π.left

namespace SmoothOnSchemes

/-- The identity 1-morphism of a scheme slice is smooth on schemes. -/
instance id {B : Scheme.{u}} {S : Over B} :
    SmoothOnSchemes (𝟙 (GroupoidsOver.slice S)) := sorry

/-- The 1-morphism of slice fibrations induced by a smooth morphism of schemes
is smooth on schemes. -/
instance ofSmooth {B : Scheme.{u}} {S T : Over B} (h : S ⟶ T)
    [AlgebraicGeometry.Smooth h.left] :
    SmoothOnSchemes (overMap h) := sorry

/-- A representing projection for a 1-morphism that is smooth on schemes is a
smooth morphism of schemes. -/
theorem spec {B : Scheme.{u}} {X : GroupoidsOver B} {S : Over B}
    (f : GroupoidsOver.slice S ⟶ X) [SmoothOnSchemes f] {S' : Over B}
    (g : GroupoidsOver.slice S' ⟶ X) {W : Over B} {π : W ⟶ S'}
    (h : RepresentsSchemeBaseChange f g W π) :
    AlgebraicGeometry.Smooth π.left := sorry

/-- A 1-morphism that is smooth on schemes is relatively representable. -/
theorem relativelyRepresentable {B : Scheme.{u}} {X : GroupoidsOver B}
    {S : Over B} (f : GroupoidsOver.slice S ⟶ X) [SmoothOnSchemes f] :
    FiberedCategoryOver.Groupoids.relativelyRepresentable f := sorry

/-- A relatively representable 1-morphism from a scheme slice is smooth on
schemes when every representing projection is a smooth morphism of schemes. -/
theorem of {B : Scheme.{u}} {X : GroupoidsOver B} {S : Over B}
    {f : GroupoidsOver.slice S ⟶ X}
    (hrep : FiberedCategoryOver.Groupoids.relativelyRepresentable f)
    (hsm : ∀ ⦃S' : Over B⦄ (g : GroupoidsOver.slice S' ⟶ X)
      (W : Over B) (π : W ⟶ S'),
      RepresentsSchemeBaseChange f g W π → AlgebraicGeometry.Smooth π.left) :
    SmoothOnSchemes f := ⟨hrep, hsm⟩

/-- A 1-morphism from a scheme slice is smooth on schemes if and only if it is
relatively representable and every representing projection is a smooth morphism
of schemes. -/
theorem iff {B : Scheme.{u}} {X : GroupoidsOver B} {S : Over B}
    (f : GroupoidsOver.slice S ⟶ X) :
    SmoothOnSchemes f ↔
      FiberedCategoryOver.Groupoids.relativelyRepresentable f ∧
        ∀ ⦃S' : Over B⦄ (g : GroupoidsOver.slice S' ⟶ X) (W : Over B)
          (π : W ⟶ S'),
          RepresentsSchemeBaseChange f g W π →
            AlgebraicGeometry.Smooth π.left := sorry

end SmoothOnSchemes

end AlgebraicGeometry.Groupoids.Hom
