/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.StrongTrans
public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Stable.StrongTrans
public import ReasLib.CategoryTheory.Fibered.Stack.Inertia.Pseudofunctor.Computations.Basic

/-!
# Strong inertia transformations on stacks

The forgetful morphism and identity-automorphism section, assembled as strong transformations
of the absolute-inertia pseudofunctor on stacks.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace StackOver.Inertia

variable (J : GrothendieckTopology C)

/-- Forgetting the selected automorphism is a strong transformation from stack inertia to the
identity pseudofunctor. -/
@[stacks 042H "stack inertia forgetful strong transformation"]
def forget.strongTrans :
    Pseudofunctor.StrongTrans
      ((pseudofunctor J) :
        Pseudofunctor
          (StackOver.{u, v, max w vS, vS} J)
          (StackOver.{u, v, max w vS, vS} J))
      (Pseudofunctor.id (StackOver.{u, v, max w vS, vS} J)) :=
  ObjectProperty.FullSubbicategory.StrongTrans.toId
    (FiberedCategoryOver.Inertia.strictPseudofunctor C)
    (map_mem J)
    (FiberedCategoryOver.Inertia.forget.strongTrans C)

namespace forget.strongTrans

/-- The component of the stack-inertia forgetful transformation is the bundled forgetful
morphism. -/
@[simp]
theorem app (X : StackOver.{u, v, max w vS, vS} J) :
    (forget.strongTrans J).app X = StackOver.inertia.forget X := sorry

/-- The naturality isomorphism of stack-inertia forgetting is the full-subbicategory lift of the
fibred-category naturality isomorphism. -/
@[simp]
theorem naturality {X Y : StackOver.{u, v, max w vS, vS} J} (F : X ⟶ Y) :
    (forget.strongTrans J).naturality F =
      Bicategory.InducedBicategory.isoMk
        ((FiberedCategoryOver.Inertia.forget.strongTrans C).naturality
          (StackOver.Hom.toMor F)) := sorry

/-- The ambient forward cell of stack-inertia forgetful naturality is the corresponding
fibred-category cell. -/
@[simp]
theorem naturality.hom.toAmbient
    {X Y : StackOver.{u, v, max w vS, vS} J} (F : X ⟶ Y) :
    ((forget.strongTrans J).naturality F).hom.hom =
      ((FiberedCategoryOver.Inertia.forget.strongTrans C).naturality
        (StackOver.Hom.toMor F)).hom := sorry

/-- The ambient inverse cell of stack-inertia forgetful naturality is the corresponding
fibred-category cell. -/
@[simp]
theorem naturality.inv.toAmbient
    {X Y : StackOver.{u, v, max w vS, vS} J} (F : X ⟶ Y) :
    ((forget.strongTrans J).naturality F).inv.hom =
      ((FiberedCategoryOver.Inertia.forget.strongTrans C).naturality
        (StackOver.Hom.toMor F)).inv := sorry

end forget.strongTrans

/-- The identity-automorphism section is a strong transformation from the identity
pseudofunctor to stack inertia. -/
@[stacks 04Z3 "stack inertia identity-section strong transformation"]
def identitySection.strongTrans :
    Pseudofunctor.StrongTrans
      (Pseudofunctor.id (StackOver.{u, v, max w vS, vS} J))
      ((pseudofunctor J) :
        Pseudofunctor
          (StackOver.{u, v, max w vS, vS} J)
          (StackOver.{u, v, max w vS, vS} J)) :=
  ObjectProperty.FullSubbicategory.StrongTrans.fromId
    (FiberedCategoryOver.Inertia.strictPseudofunctor C)
    (map_mem J)
    (FiberedCategoryOver.Inertia.identitySection.strongTrans C)

namespace identitySection.strongTrans

/-- The component of the stack-inertia identity-section transformation is the bundled identity
section. -/
@[simp]
theorem app (X : StackOver.{u, v, max w vS, vS} J) :
    (identitySection.strongTrans J).app X =
      StackOver.inertia.identitySection X := sorry

/-- The naturality isomorphism of the stack-inertia identity section is the full-subbicategory
lift of the fibred-category naturality isomorphism. -/
@[simp]
theorem naturality {X Y : StackOver.{u, v, max w vS, vS} J} (F : X ⟶ Y) :
    (identitySection.strongTrans J).naturality F =
      ObjectProperty.FullSubbicategory.StrongTrans.FromId.naturality
        (P := IsStack.OnSite.objectProperty J)
        (FiberedCategoryOver.Inertia.strictPseudofunctor C)
        (map_mem J)
        (FiberedCategoryOver.Inertia.identitySection.strongTrans C) F := sorry

/-- The ambient forward cell of stack identity-section naturality is the corresponding
fibred-category cell. -/
@[simp]
theorem naturality.hom.toAmbient
    {X Y : StackOver.{u, v, max w vS, vS} J} (F : X ⟶ Y) :
    ((identitySection.strongTrans J).naturality F).hom.hom =
      ((FiberedCategoryOver.Inertia.identitySection.strongTrans C).naturality
        (StackOver.Hom.toMor F)).hom := sorry

/-- The ambient inverse cell of stack identity-section naturality is the corresponding
fibred-category cell. -/
@[simp]
theorem naturality.inv.toAmbient
    {X Y : StackOver.{u, v, max w vS, vS} J} (F : X ⟶ Y) :
    ((identitySection.strongTrans J).naturality F).inv.hom =
      ((FiberedCategoryOver.Inertia.identitySection.strongTrans C).naturality
        (StackOver.Hom.toMor F)).inv := sorry

end identitySection.strongTrans

end StackOver.Inertia

end CategoryTheory
