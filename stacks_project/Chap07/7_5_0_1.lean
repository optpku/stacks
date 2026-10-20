module

public import ReasLib.CategoryTheory.Comma.StructuredArrow
public import ReasLib.CategoryTheory.Functor.StructuredArrow.Hom
public import StacksCheckRecall.CommandCrossRef
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable (u : C ⥤ D) (V : D)

/- 7.5.0.1: for a functor u : C ⥤ D and an object V : D, the indexing
category I^u_V has objects (U, φ) with U : C and φ : V ⟶ u.obj U, and
morphisms f : U ⟶ U' in C satisfying φ ≫ u.map f = φ'. This is the
category StructuredArrow V u. -/
@[stacks 053L] #check
  (CategoryTheory.StructuredArrow.objEquiv V u :
    StructuredArrow V u ≃ (Σ U : C, V ⟶ u.obj U))

#check (inferInstance : Category (StructuredArrow V u))
#check (CategoryTheory.StructuredArrow.mk :
    ∀ {U : C}, (V ⟶ u.obj U) → StructuredArrow V u)

variable (X Y : StructuredArrow V u) (f : X ⟶ Y)

#check (CategoryTheory.StructuredArrow.homEquiv X Y :
    (X ⟶ Y) ≃ {g : X.right ⟶ Y.right // X.hom ≫ u.map g = Y.hom})
#check (X.right : C)
#check (X.hom : V ⟶ u.obj X.right)
variable (rightMap : X.right ⟶ Y.right) (triangle : X.hom ≫ u.map rightMap = Y.hom)

#check (CategoryTheory.StructuredArrow.homMk rightMap triangle : X ⟶ Y)
#check (f.right : X.right ⟶ Y.right)
#check (CategoryTheory.StructuredArrow.w f : X.hom ≫ u.map f.right = Y.hom)
#check (CategoryTheory.StructuredArrow.hom_eq_iff :
    ∀ (f g : X ⟶ Y), f = g ↔ f.right = g.right)
