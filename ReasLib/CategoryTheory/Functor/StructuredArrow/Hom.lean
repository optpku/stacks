module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Morphisms of structured arrows

This file gives the reusable Hom API for `StructuredArrow`. A morphism is identified with its
right component together with the defining triangle, independently of any fibered-category
application. When the source structure map is an isomorphism, a second interface rewrites the
triangle using its inverse.
-/

@[expose] public section

universe uC vC uD vD

namespace CategoryTheory.StructuredArrow

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable {S : D} {T : C ⥤ D}

/-- A right-component map lifts to a structured-arrow morphism exactly when its defining
triangle commutes. -/
theorem exists_hom_right_iff
    (A B : StructuredArrow S T) (g : A.right ⟶ B.right) :
    (∃ f : A ⟶ B, f.right = g) ↔ A.hom ≫ T.map g = B.hom := sorry

/-- The right component of a structured-arrow morphism satisfies the defining triangle. -/
theorem homEquiv.condition
    (A B : StructuredArrow S T) (f : A ⟶ B) :
    A.hom ≫ T.map f.right = B.hom := sorry

/-- Reconstructing a structured-arrow morphism from its right component recovers the original
morphism. -/
theorem homEquiv.leftInverse
    (A B : StructuredArrow S T) (f : A ⟶ B) :
    StructuredArrow.homMk f.right (homEquiv.condition A B f) = f := sorry

/-- Reconstructing and then projecting a compatible right component recovers the original
subtype element. -/
theorem homEquiv.rightInverse
    (A B : StructuredArrow S T)
    (g : {g : A.right ⟶ B.right // A.hom ≫ T.map g = B.hom}) :
    (⟨(StructuredArrow.homMk g.1 g.2).right,
        homEquiv.condition A B (StructuredArrow.homMk g.1 g.2)⟩ :
      {h : A.right ⟶ B.right // A.hom ≫ T.map h = B.hom}) = g := sorry

/-- Structured-arrow morphisms are canonically equivalent to right-component maps satisfying
the defining triangle. This is the intrinsic Hom interface; it requires no invertibility
assumption. -/
@[stacks 02Y5 "(2) intrinsic structured-arrow Hom equivalence"]
def homEquiv (A B : StructuredArrow S T) :
    (A ⟶ B) ≃ {g : A.right ⟶ B.right // A.hom ≫ T.map g = B.hom} where
  toFun f := ⟨f.right, homEquiv.condition A B f⟩
  invFun g := StructuredArrow.homMk g.1 g.2
  left_inv := homEquiv.leftInverse A B
  right_inv := homEquiv.rightInverse A B

/-- The intrinsic Hom equivalence sends a structured-arrow morphism to its right component. -/
@[simp]
theorem homEquiv.apply_val
    (A B : StructuredArrow S T) (f : A ⟶ B) :
    ((homEquiv A B) f).1 = f.right := sorry

/-- The inverse intrinsic Hom equivalence has the supplied compatible map as right component. -/
@[simp]
theorem homEquiv.symm_apply_right
    (A B : StructuredArrow S T)
    (g : {g : A.right ⟶ B.right // A.hom ≫ T.map g = B.hom}) :
    ((homEquiv A B).symm g).right = g.1 := sorry

noncomputable section

/-- If the source structure map is invertible, the defining triangle is equivalent to the
inverse-form equation for the right component. -/
theorem comp_eq_iff_map_eq
    (A B : StructuredArrow S T) [IsIso A.hom]
    (g : A.right ⟶ B.right) :
    A.hom ≫ T.map g = B.hom ↔ T.map g = (asIso A.hom).inv ≫ B.hom := sorry

/-- Lemma 4.42.1 (Stacks 02Y5) (2), constructor form: build a structured-arrow morphism from an
inverse-form equation for its right component. Only the source structure map must be
invertible. -/
@[stacks 02Y5 "(2) reusable structured-arrow morphism constructor"]
def homMkInv
    (A B : StructuredArrow S T) [IsIso A.hom]
    (g : A.right ⟶ B.right)
    (h : T.map g = (asIso A.hom).inv ≫ B.hom) : A ⟶ B :=
  StructuredArrow.homMk g ((comp_eq_iff_map_eq A B g).mpr h)

/-- The right component of `homMkInv` is the supplied morphism. -/
@[simp]
theorem homMkInv_right
    (A B : StructuredArrow S T) [IsIso A.hom]
    (g : A.right ⟶ B.right)
    (h : T.map g = (asIso A.hom).inv ≫ B.hom) :
    (homMkInv A B g h).right = g := sorry

/-- The right component of a structured-arrow morphism satisfies the inverse-form equation when
the source structure map is invertible. -/
theorem homEquivInv.condition
    (A B : StructuredArrow S T) [IsIso A.hom] (f : A ⟶ B) :
    T.map f.right = (asIso A.hom).inv ≫ B.hom := sorry

/-- Reconstructing a structured-arrow morphism through the inverse-form interface recovers the
original morphism. -/
theorem homEquivInv.leftInverse
    (A B : StructuredArrow S T) [IsIso A.hom] (f : A ⟶ B) :
    homMkInv A B f.right (homEquivInv.condition A B f) = f := sorry

/-- Projecting a morphism reconstructed from inverse-form data recovers the original subtype
element. -/
theorem homEquivInv.rightInverse
    (A B : StructuredArrow S T) [IsIso A.hom]
    (g : {g : A.right ⟶ B.right // T.map g = (asIso A.hom).inv ≫ B.hom}) :
    (⟨(homMkInv A B g.1 g.2).right,
        homEquivInv.condition A B (homMkInv A B g.1 g.2)⟩ :
      {h : A.right ⟶ B.right // T.map h = (asIso A.hom).inv ≫ B.hom}) = g := sorry

/-- Lemma 4.42.1 (Stacks 02Y5) (2), in reusable form: when the source structure map is
invertible, structured-arrow morphisms are canonically equivalent to right-component maps
satisfying the inverse-form equation. -/
@[stacks 02Y5 "(2) reusable structured-arrow Hom equivalence"]
def homEquivInv
    (A B : StructuredArrow S T) [IsIso A.hom] :
    (A ⟶ B) ≃
      {g : A.right ⟶ B.right // T.map g = (asIso A.hom).inv ≫ B.hom} where
  toFun f := ⟨f.right, homEquivInv.condition A B f⟩
  invFun g := homMkInv A B g.1 g.2
  left_inv := homEquivInv.leftInverse A B
  right_inv := homEquivInv.rightInverse A B

/-- The inverse-form Hom equivalence sends a structured-arrow morphism to its right component. -/
@[simp]
theorem homEquivInv.apply_val
    (A B : StructuredArrow S T) [IsIso A.hom] (f : A ⟶ B) :
    ((homEquivInv A B) f).1 = f.right := sorry

/-- The inverse of the inverse-form Hom equivalence has the supplied map as right component. -/
@[simp]
theorem homEquivInv.symm_apply_right
    (A B : StructuredArrow S T) [IsIso A.hom]
    (g : {g : A.right ⟶ B.right // T.map g = (asIso A.hom).inv ≫ B.hom}) :
    ((homEquivInv A B).symm g).right = g.1 := sorry

end

end CategoryTheory.StructuredArrow

/- Axiom audit: `homEquiv`, `homMkInv`, and `homEquivInv` retain their supplied right-component
maps as explicit non-Prop data. Any statement-stage `sorryAx` reported below is confined to the
Prop-valued triangle and inverse-law fields. -/
