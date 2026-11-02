/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import ReasLib.CategoryTheory.Fibered.Fiber.Restriction

/-!
# Restriction in fibres over schemes

Chosen cartesian lifts define restriction of objects, arrows, and isomorphisms,
with identity and composition comparisons. The names in this namespace are
compatibility specialisations of `CategoryTheory.Functor.Fiber` restriction;
they use exactly the same chosen cartesian lifts.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Functor

noncomputable section

universe u

namespace AlgebraicGeometry.FiniteHilbertStack

variable {S : Scheme.{u}}
variable {𝒳 : Type (u + 1)} [Category.{u} 𝒳]

/-- Restriction of a fibre object along a morphism of `S`-schemes, obtained from a
chosen cartesian lift. -/
abbrev restrictObj {p : 𝒳 ⥤ Over S} [p.IsFibered] {U Z : Over S}
    (ξ : p.Fiber U) (f : Z ⟶ U) : p.Fiber Z :=
  Fiber.restrictObj ξ f

/-- The underlying total object of `restrictObj` is the chosen cartesian pullback. -/
theorem restrictObj_val {p : 𝒳 ⥤ Over S} [p.IsFibered] {U Z : Over S}
    (ξ : p.Fiber U) (f : Z ⟶ U) :
    (restrictObj ξ f).1 = IsPreFibered.pullbackObj ξ.property f := rfl

/-- Restriction along equal base morphisms gives canonically isomorphic fibre objects. -/
abbrev restrictObj_eq {p : 𝒳 ⥤ Over S} [p.IsFibered] {U Z : Over S}
    (ξ : p.Fiber U) {f g : Z ⟶ U} (h : f = g) :
    restrictObj ξ f ≅ restrictObj ξ g :=
  Fiber.restrictObj_eq ξ h

/-- The unique comparison induced by a cartesian lift, with explicit certificates. -/
abbrev cartesianMap {p : 𝒳 ⥤ Over S} {R T : Over S} {a b a' : 𝒳}
    (f : R ⟶ T) (φ : a ⟶ b) (hφ : p.IsCartesian f φ)
    (φ' : a' ⟶ b) (hφ' : p.IsHomLift f φ') : a' ⟶ a :=
  Fiber.cartesianMap f φ hφ φ' hφ'

/-- The comparison `cartesianMap` is vertical over the identity of the domain. -/
theorem cartesianMap_isHomLift {p : 𝒳 ⥤ Over S} {R T : Over S} {a b a' : 𝒳}
    (f : R ⟶ T) (φ : a ⟶ b) (hφ : p.IsCartesian f φ)
    (φ' : a' ⟶ b) (hφ' : p.IsHomLift f φ') :
    p.IsHomLift (𝟙 R) (cartesianMap f φ hφ φ' hφ') :=
  Fiber.cartesianMap_isHomLift f φ hφ φ' hφ'

/-- A fibre morphism over `U` restricts along `f : Z ⟶ U` by the universal property
of the chosen cartesian lift. -/
@[no_expose]
abbrev restrictHom {p : 𝒳 ⥤ Over S} [p.IsFibered] {U Z : Over S}
    {ξ ξ' : p.Fiber U} (φ : ξ ⟶ ξ') (f : Z ⟶ U) :
    restrictObj ξ f ⟶ restrictObj ξ' f :=
  Fiber.restrictHom φ f

/-- Restriction of a fibre isomorphism along a morphism of `S`-schemes. -/
abbrev restrictIso {p : 𝒳 ⥤ Over S} [p.IsFibered] {U Z : Over S}
    {ξ ξ' : p.Fiber U} (e : ξ ≅ ξ') (f : Z ⟶ U) :
    restrictObj ξ f ≅ restrictObj ξ' f :=
  Fiber.restrictIso e f

/-- Restriction along the identity recovers the original fibre object. -/
@[no_expose]
abbrev restrictObj_id {p : 𝒳 ⥤ Over S} [p.IsFibered] {U : Over S}
    (ξ : p.Fiber U) : restrictObj ξ (𝟙 U) ≅ ξ :=
  Fiber.restrictObj_id ξ

/-- Successive restrictions along `f` then `g` agree with restriction along `g ≫ f`. -/
abbrev restrictObj_comp {p : 𝒳 ⥤ Over S} [p.IsFibered]
    {U V W : Over S} (ξ : p.Fiber U) (f : V ⟶ U) (g : W ⟶ V) :
    restrictObj (restrictObj ξ f) g ≅ restrictObj ξ (g ≫ f) :=
  Fiber.restrictObj_comp ξ f g

end AlgebraicGeometry.FiniteHilbertStack
