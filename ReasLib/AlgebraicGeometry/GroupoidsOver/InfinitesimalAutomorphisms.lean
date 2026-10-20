/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.FiberedCategory.Cartesian
public import ReasLib.CategoryTheory.Fibered.Fiber.Isomorphism
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Lifts
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Cartesian

/-!
# Infinitesimal automorphisms of a fibered lift

For a lift `x'` of a fibre object `x` along an `S`-algebra map `A' ⟶ A`, the group
`Inf(x'/x)` is the equalizer subgroup of fibre automorphisms of the codomain of `x'`
that fix the underlying total morphism of the lift. This coincides with the kernel of
restriction `Aut(x') →* Aut(x)` along the cartesian universal property of the lift.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {X : GroupoidsOver S}
variable {A A' : CommRingCat.{u}} {σA : Spec A ⟶ S} {σA' : Spec A' ⟶ S}
variable {x : X.p.Fiber (Over.mk σA)} {fA : A' ⟶ A}
variable {hfA : Spec.map fA ≫ σA' = σA}

/-- A lift morphism is cartesian over its displayed `S`-algebra map. -/
instance lift_isCartesian (x' : liftCat x fA hfA) :
    X.p.IsCartesian (specOverHom fA hfA) x'.hom := sorry

/-- Postcomposition of a lift morphism with a fibre endomorphism of its codomain still
lifts the same `S`-algebra map. -/
theorem lift_comp_fiber_isHomLift (x' : liftCat x fA hfA)
    (η : x'.codomain ⟶ x'.codomain) :
    X.p.IsHomLift (specOverHom fA hfA)
      (x'.hom ≫ Fiber.fiberInclusion.map η) := sorry

/-- The cartesian factor of a total morphism through a lift, as a vertical endomorphism
of the source fibre object. -/
def restrictAutArrow (x' : liftCat x fA hfA)
    (ψ : Fiber.fiberInclusion.obj x ⟶ x'.right)
    (hψ : X.p.IsHomLift (specOverHom fA hfA) ψ) :
    Fiber.fiberInclusion.obj x ⟶ Fiber.fiberInclusion.obj x :=
  @IsCartesian.map _ _ _ _ X.p _ _ _ _ (specOverHom fA hfA) x'.hom
    (lift_isCartesian x') (Fiber.fiberInclusion.obj x) ψ hψ

/-- The cartesian factor of a lift through `x'.hom` is vertical over `Spec(A)`. -/
theorem restrictAutArrow_isHomLift (x' : liftCat x fA hfA)
    (ψ : Fiber.fiberInclusion.obj x ⟶ x'.right)
    (hψ : X.p.IsHomLift (specOverHom fA hfA) ψ) :
    X.p.IsHomLift (𝟙 (Over.mk σA)) (restrictAutArrow x' ψ hψ) :=
  @IsCartesian.map_isHomLift _ _ _ _ X.p _ _ _ _ (specOverHom fA hfA) x'.hom
    (lift_isCartesian x') (Fiber.fiberInclusion.obj x) ψ hψ

/-- The group of infinitesimal automorphisms `Inf(x'/x)` of a lift `x'` of `x`. As a
subgroup of `Aut(x'.codomain)` it is the equalizer of postcomposition with `x'.hom`. -/
def infinitesimalAut (x' : liftCat x fA hfA) : Subgroup (Aut x'.codomain) where
  carrier := {α | x'.hom ≫ Fiber.fiberInclusion.map α.hom = x'.hom}
  mul_mem' := sorry
  one_mem' := sorry
  inv_mem' := sorry

/-- Membership in `infinitesimalAut` is the equalizer condition that a fibre
automorphism of the lift becomes the identity after composing with `x'.hom`. -/
theorem mem_infinitesimalAut (x' : liftCat x fA hfA) (α : Aut x'.codomain) :
    α ∈ infinitesimalAut x' ↔ x'.hom ≫ Fiber.fiberInclusion.map α.hom = x'.hom := sorry

/-- Restriction `Aut(x') →* Aut(x)` along a lift, sending a fibre automorphism of the
codomain to the unique vertical automorphism of `x` obtained from the cartesian
universal property of `x'.hom`. -/
def restrictAut (x' : liftCat x fA hfA) : Aut x'.codomain →* Aut x where
  toFun α :=
    Fiber.isoMk
      { hom :=
          restrictAutArrow x' (x'.hom ≫ Fiber.fiberInclusion.map α.hom)
            (lift_comp_fiber_isHomLift x' α.hom)
        inv :=
          restrictAutArrow x' (x'.hom ≫ Fiber.fiberInclusion.map α.inv)
            (lift_comp_fiber_isHomLift x' α.inv)
        hom_inv_id := sorry
        inv_hom_id := sorry }
      (restrictAutArrow_isHomLift x' (x'.hom ≫ Fiber.fiberInclusion.map α.hom)
        (lift_comp_fiber_isHomLift x' α.hom))
  map_one' := sorry
  map_mul' := sorry

/-- The underlying total morphism of `restrictAut x' α` is the cartesian factor of
`x'.hom ≫ α` through `x'.hom`. -/
theorem restrictAut_apply (x' : liftCat x fA hfA) (α : Aut x'.codomain) :
    Fiber.fiberInclusion.map (restrictAut x' α).hom =
      restrictAutArrow x' (x'.hom ≫ Fiber.fiberInclusion.map α.hom)
        (lift_comp_fiber_isHomLift x' α.hom) := sorry

/-- Restriction along a lift is characterised by the commutative square
`restrictAut(α) ≫ x'.hom = x'.hom ≫ α`. -/
theorem restrictAut_comp (x' : liftCat x fA hfA) (α : Aut x'.codomain) :
    Fiber.fiberInclusion.map (restrictAut x' α).hom ≫ x'.hom =
      x'.hom ≫ Fiber.fiberInclusion.map α.hom := sorry

/-- The equalizer subgroup `infinitesimalAut` is the kernel of `restrictAut`. -/
theorem infinitesimalAut_eq_ker (x' : liftCat x fA hfA) :
    infinitesimalAut x' = (restrictAut x').ker := sorry

end AlgebraicGeometry.GroupoidsOver
