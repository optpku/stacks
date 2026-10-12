/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Explicit construction of fiber morphisms

Mathlib's `Functor.Fiber.homMk` receives verticality through typeclass search. This leaf provides
the ordinary-argument constructor for arrows whose `IsHomLift` certificate is explicit data.
-/

@[expose] public section

universe uC uS vC vS

namespace CategoryTheory.Functor.IsHomLift

variable {C : Type uC} {S : Type uS} [Category.{vC} C] [Category.{vS} S]
variable {p : S ⥤ C} {U V : C} {x y : S}

/-- Inverting an isomorphism preserves an explicitly supplied lift certificate. This is the
ordinary-argument counterpart of Mathlib's `inv_lift_inv` instance. -/
theorem inv_lift_inv_of (f : U ≅ V) (e : x ≅ y)
    (h : p.IsHomLift f.hom e.hom) :
    p.IsHomLift f.inv e.inv := sorry

/-- The inverse of an explicitly vertical isomorphism is explicitly vertical. -/
theorem lift_id_inv_of (e : x ≅ y) (h : p.IsHomLift (𝟙 U) e.hom) :
    p.IsHomLift (𝟙 U) e.inv := sorry

end CategoryTheory.Functor.IsHomLift

namespace CategoryTheory.Functor.Fiber.Hom

variable {C : Type uC} {S : Type uS} [Category.{vC} C] [Category.{vS} S]
variable {p : S ⥤ C} {U : C} {x y : p.Fiber U}

/-- Package an ambient arrow as a morphism in a fixed fiber using an explicit verticality
certificate. This is the ordinary-argument boundary for Mathlib's typeclass-driven
`Functor.Fiber.homMk`. -/
def mk (φ : x.1 ⟶ y.1) (hφ : p.IsHomLift (𝟙 U) φ) : x ⟶ y :=
  ⟨φ, hφ⟩

/-- The ambient arrow underlying `Hom.mk` is the supplied arrow. -/
@[simp]
theorem mk.val (φ : x.1 ⟶ y.1) (hφ : p.IsHomLift (𝟙 U) φ) :
    (mk φ hφ).1 = φ := sorry

end CategoryTheory.Functor.Fiber.Hom
