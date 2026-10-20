module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Base
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver.Hom.Construction
public import ReasLib.AlgebraicGeometry.FiniteHilbertStack.Specializations

/-!
# Canonical base fibres of finite Hilbert stacks

The identity fibration on `(Sch/S)_fppf` supplies the canonical fibre objects and
comparison isomorphisms used to specialise `H_d(𝒳/𝒴)` to `H_d(𝒳) = H_d(𝒳/S)`
and `H_d = H_d(S/S)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.FiniteHilbertStack

variable {S : Scheme.{u}}

/-- The identity fibration on `(Sch/S)_fppf`. -/
abbrev schemeBase (S : Scheme.{u}) : GroupoidsOver S :=
  base.{u + 1, u, u + 1} (Over S)

/-- `schemeBase S` is the universe-resized identity fibration on `Over S`. -/
theorem schemeBase_eq (S : Scheme.{u}) :
    schemeBase S = base.{u + 1, u, u + 1} (Over S) :=
  rfl

/-- The underlying groupoid fibration of a stack in groupoids over `(Sch/S)_fppf`. -/
abbrev asGroupoidsOver
    (𝒳 : StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)) :
    GroupoidsOver S :=
  𝒳.toGroupoids

/-- `asGroupoidsOver` is the underlying groupoid-fibred category. -/
theorem asGroupoidsOver_eq
    (𝒳 : StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)) :
    asGroupoidsOver 𝒳 = 𝒳.toGroupoids :=
  rfl

/-- The underlying groupoid-fibred 1-morphism of a morphism of stacks in groupoids. -/
abbrev asGroupoidsOverMor
    {𝒳 𝒴 : StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)}
    (F : 𝒳 ⟶ 𝒴) :
    asGroupoidsOver 𝒳 ⟶ asGroupoidsOver 𝒴 :=
  StackOver.Groupoids.Hom.toGroupoidsMor F

/-- `asGroupoidsOverMor` is `toGroupoidsMor`. -/
theorem asGroupoidsOverMor_eq
    {𝒳 𝒴 : StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)}
    (F : 𝒳 ⟶ 𝒴) :
    asGroupoidsOverMor F = StackOver.Groupoids.Hom.toGroupoidsMor F :=
  rfl

/-- The structure 1-morphism `𝒳 ⟶ S` used to form `H_d(𝒳) = H_d(𝒳/S)`. -/
abbrev toSchemeProjection
    (𝒳 : StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)) :
    asGroupoidsOver 𝒳 ⟶ schemeBase S :=
  baseProjection.{u + 1, u, u + 1} (asGroupoidsOver 𝒳)

/-- `toSchemeProjection 𝒳` is the canonical `baseProjection` of `𝒳`. -/
theorem toSchemeProjection_eq
    (𝒳 : StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)) :
    toSchemeProjection 𝒳 = baseProjection.{u + 1, u, u + 1} (asGroupoidsOver 𝒳) :=
  rfl

/-- The canonical section of the identity fibration on `(Sch/S)_fppf`. -/
abbrev schemeBaseSection (S : Scheme.{u}) : Over S ⥤ (schemeBase S).total :=
  baseSection.{u + 1, u, u + 1} (Over S)

/-- The canonical fibre object of the identity fibration over a test scheme `U`. -/
def baseFiber (U : Over S) : (schemeBase S).p.Fiber U :=
  Fiber.mk (a := (schemeBaseSection S).obj U) rfl

/-- The underlying total object of `baseFiber U` is the canonical section at `U`. -/
theorem baseFiber_val (U : Over S) :
    (baseFiber U).1 = (schemeBaseSection S).obj U :=
  rfl

/-- The structure morphism of the identity fibration lifts along the canonical section. -/
theorem schemeBaseSection_isHomLift {U Z : Over S} (π : Z ⟶ U) :
    (schemeBase S).p.IsHomLift π ((schemeBaseSection S).map π) :=
  sorry

/-- The canonical section morphism is cartesian for the identity fibration. -/
theorem schemeBaseSection_isCartesian {U Z : Over S} (π : Z ⟶ U) :
    (schemeBase S).p.IsCartesian π ((schemeBaseSection S).map π) :=
  sorry

/-- The cartesian restriction comparison followed by its reverse is the identity. -/
theorem baseRestrictUnderlyingIso_hom_inv_id {U Z : Over S} (π : Z ⟶ U) :
    (cartesianMap π ((schemeBaseSection S).map π) (schemeBaseSection_isCartesian π)
      (IsPreFibered.pullbackMap (baseFiber U).property π)
      (IsPreFibered.pullbackMap.IsCartesian (baseFiber U).property π).toIsHomLift) ≫
      (cartesianMap π (IsPreFibered.pullbackMap (baseFiber U).property π)
      (IsPreFibered.pullbackMap.IsCartesian (baseFiber U).property π)
      ((schemeBaseSection S).map π) (schemeBaseSection_isHomLift π)) = 𝟙 (restrictObj (baseFiber U) π).1 :=
  sorry

/-- The reverse cartesian restriction comparison followed by the forward comparison is the identity. -/
theorem baseRestrictUnderlyingIso_inv_hom_id {U Z : Over S} (π : Z ⟶ U) :
    (cartesianMap π (IsPreFibered.pullbackMap (baseFiber U).property π)
      (IsPreFibered.pullbackMap.IsCartesian (baseFiber U).property π)
      ((schemeBaseSection S).map π) (schemeBaseSection_isHomLift π)) ≫
      (cartesianMap π ((schemeBaseSection S).map π) (schemeBaseSection_isCartesian π)
      (IsPreFibered.pullbackMap (baseFiber U).property π)
      (IsPreFibered.pullbackMap.IsCartesian (baseFiber U).property π).toIsHomLift) = 𝟙 (baseFiber Z).1 :=
  sorry

/-- The underlying comparison identifying a cartesian restriction of `baseFiber U`
with `baseFiber Z`. -/
def baseRestrictUnderlyingIso {U Z : Over S} (π : Z ⟶ U) :
    (restrictObj (baseFiber U) π).1 ≅ (baseFiber Z).1 where
  hom :=
    cartesianMap π ((schemeBaseSection S).map π) (schemeBaseSection_isCartesian π)
      (IsPreFibered.pullbackMap (baseFiber U).property π)
      (IsPreFibered.pullbackMap.IsCartesian (baseFiber U).property π).toIsHomLift
  inv :=
    cartesianMap π (IsPreFibered.pullbackMap (baseFiber U).property π)
      (IsPreFibered.pullbackMap.IsCartesian (baseFiber U).property π)
      ((schemeBaseSection S).map π) (schemeBaseSection_isHomLift π)
  hom_inv_id := baseRestrictUnderlyingIso_hom_inv_id π
  inv_hom_id := baseRestrictUnderlyingIso_inv_hom_id π

/-- The forward comparison of `baseRestrictUnderlyingIso` is vertical over `Z`. -/
theorem baseRestrictUnderlyingIso_isHomLift {U Z : Over S} (π : Z ⟶ U) :
    (schemeBase S).p.IsHomLift (𝟙 Z) (baseRestrictUnderlyingIso π).hom :=
  sorry

/-- Restriction of the canonical fibre object along `π : Z ⟶ U` recovers `baseFiber Z`. -/
def baseRestrictIso {U Z : Over S} (π : Z ⟶ U) :
    restrictObj (baseFiber U) π ≅ baseFiber Z :=
  Fiber.isoMk (baseRestrictUnderlyingIso π) (baseRestrictUnderlyingIso_isHomLift π)

/-- The image of a fibre object of `X` under `baseProjection` is the canonical fibre object. -/
def baseProjectionFiberIso {X : GroupoidsOver S} {Z : Over S} (x : X.p.Fiber Z) :
    (fiberFunctor (baseProjection.{u + 1, u, u + 1} X) Z).obj x ≅ baseFiber Z :=
  Fiber.isoMk
    (eqToIso (congrArg (schemeBaseSection S).obj x.property))
    (IsHomLift.eqToHom_domain_lift_id
      (congrArg (schemeBaseSection S).obj x.property)
      ((fiberFunctor (baseProjection.{u + 1, u, u + 1} X) Z).obj x).property)

/-- The identity 1-morphism of the identity fibration acts as the identity on `baseFiber`. -/
def identityFiberIso (Z : Over S) :
    (fiberFunctor (𝟙 (schemeBase S)) Z).obj (baseFiber Z) ≅ baseFiber Z :=
  Fiber.isoMk (Iso.refl _) (IsHomLift.id (baseFiber Z).property)

/-- The canonical isomorphism `α_S` for an object of `H_d(𝒳) = H_d(𝒳/S)`. -/
def ofStackIso {X : GroupoidsOver S} {U Z : Over S} (π : Z ⟶ U) (x : X.p.Fiber Z) :
    restrictObj (baseFiber U) π ≅
      (fiberFunctor (baseProjection.{u + 1, u, u + 1} X) Z).obj x :=
  baseRestrictIso π ≪≫ (baseProjectionFiberIso x).symm

/-- The canonical isomorphism `α_S` for an object of `H_d = H_d(S/S)`. -/
def ofSchemeIso {U Z : Over S} (π : Z ⟶ U) :
    restrictObj (baseFiber U) π ≅
      (fiberFunctor (𝟙 (schemeBase S)) Z).obj (baseFiber Z) :=
  baseRestrictIso π ≪≫ (identityFiberIso Z).symm

/-- `ofStackIso` is the composite of `baseRestrictIso` with the base-projection comparison. -/
theorem ofStackIso_eq {X : GroupoidsOver S} {U Z : Over S} (π : Z ⟶ U) (x : X.p.Fiber Z) :
    ofStackIso π x = baseRestrictIso π ≪≫ (baseProjectionFiberIso x).symm :=
  rfl

/-- `ofSchemeIso` is the composite of `baseRestrictIso` with the identity-fibre comparison. -/
theorem ofSchemeIso_eq {U Z : Over S} (π : Z ⟶ U) :
    ofSchemeIso π = baseRestrictIso π ≪≫ (identityFiberIso Z).symm :=
  rfl

end AlgebraicGeometry.FiniteHilbertStack
