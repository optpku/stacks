module

public import ReasLib.CategoryTheory.Fibered.Stack.Over.TwoFibreProduct.Pseudofunctor.Projections.Construction

/-!
# Component computations for stack-valued two-fibre-product projections

These lemmas expose the ambient and stack-valued components of the canonical projection
transformations, together with their forgetful readouts.
-/

@[expose] public section

noncomputable section

universe u v w vB

namespace CategoryTheory

open Bicategory ObjectProperty
open scoped Bicategory Pseudofunctor.StrongTrans

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

namespace StackOver.TwoFibreProduct

/-- The ambient first-projection component is the neutral first projection on the
componentwise-forgotten cospan. -/
@[simp, stacks 026G "ambient stack two-fibre-product first projection computation"]
theorem pseudofunctor.fst.ambient.app
    (S : Bicategory.Cospan
      (StackOver.{u, v, max w (max u (max v vB)), max v vB} J)) :
    (pseudofunctor.fst.ambient J).app S =
      (FiberedCategoryOver.TwoFibreProduct.pseudofunctor.fst
          (C := C)).app
          ((Bicategory.Cospan.map
            (StackOver.forget J).toPseudofunctor).obj S) ≫
        𝟙 ((StackOver.forget J).obj S.left) := sorry

/-- The ambient second-projection component is the neutral second projection on the
componentwise-forgotten cospan. -/
@[simp, stacks 026G "ambient stack two-fibre-product second projection computation"]
theorem pseudofunctor.snd.ambient.app
    (S : Bicategory.Cospan
      (StackOver.{u, v, max w (max u (max v vB)), max v vB} J)) :
    (pseudofunctor.snd.ambient J).app S =
      (FiberedCategoryOver.TwoFibreProduct.pseudofunctor.snd
          (C := C)).app
          ((Bicategory.Cospan.map
            (StackOver.forget J).toPseudofunctor).obj S) ≫
        𝟙 ((StackOver.forget J).obj S.right) := sorry

/-- The first-projection component is the ambient component regarded as a stack morphism. -/
@[simp, stacks 026G "stack two-fibre-product first projection computation"]
theorem pseudofunctor.fst.app
    (S : Bicategory.Cospan
      (StackOver.{u, v, max w (max u (max v vB)), max v vB} J)) :
    (pseudofunctor.fst J).app S =
      Bicategory.InducedBicategory.mkHom
        ((pseudofunctor.fst.ambient J).app S) := sorry

/-- The second-projection component is the ambient component regarded as a stack morphism. -/
@[simp, stacks 026G "stack two-fibre-product second projection computation"]
theorem pseudofunctor.snd.app
    (S : Bicategory.Cospan
      (StackOver.{u, v, max w (max u (max v vB)), max v vB} J)) :
    (pseudofunctor.snd J).app S =
      Bicategory.InducedBicategory.mkHom
        ((pseudofunctor.snd.ambient J).app S) := sorry

/-- Forgetting the first-projection component recovers its ambient component. -/
@[simp, stacks 026G "stack two-fibre-product first projection ambient readout"]
theorem pseudofunctor.fst.app.toAmbient
    (S : Bicategory.Cospan
      (StackOver.{u, v, max w (max u (max v vB)), max v vB} J)) :
    ((pseudofunctor.fst J).app S).hom =
      (pseudofunctor.fst.ambient J).app S := sorry

/-- Forgetting the second-projection component recovers its ambient component. -/
@[simp, stacks 026G "stack two-fibre-product second projection ambient readout"]
theorem pseudofunctor.snd.app.toAmbient
    (S : Bicategory.Cospan
      (StackOver.{u, v, max w (max u (max v vB)), max v vB} J)) :
    ((pseudofunctor.snd J).app S).hom =
      (pseudofunctor.snd.ambient J).app S := sorry

end StackOver.TwoFibreProduct

end CategoryTheory
