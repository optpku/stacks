/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.StrongTrans
public import ReasLib.CategoryTheory.Fibered.Stack.Inertia.Pseudofunctor.Computations.Setoids
public import ReasLib.CategoryTheory.Fibered.Stack.Inertia.Pseudofunctor.StrongTrans.Groupoids

/-!
# Strong inertia transformations on stacks in setoids

The setoid-stack transformations are obtained by restricting the groupoid-stack
transformations through the thin-fibre property.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace StackOver.Setoids.Inertia

variable (J : GrothendieckTopology C)

/-- Forgetting the selected automorphism is a strong transformation from setoid-stack inertia
to the identity pseudofunctor. -/
@[stacks 042H "setoid-stack inertia forgetful strong transformation"]
def forget.strongTrans :
    Pseudofunctor.StrongTrans
      ((pseudofunctor J) :
        Pseudofunctor
          (StackOver.Setoids.{u, v, max w vS, vS} J)
          (StackOver.Setoids.{u, v, max w vS, vS} J))
      (Pseudofunctor.id
        (StackOver.Setoids.{u, v, max w vS, vS} J)) :=
  ObjectProperty.FullSubbicategory.StrongTrans.toId
    (P := IsStack.InSetoids.objectProperty J)
    (StackOver.Groupoids.Inertia.strictPseudofunctor J)
    (map_mem J)
    (StackOver.Groupoids.Inertia.forget.strongTrans J)

namespace forget.strongTrans

/-- The component of the setoid-stack inertia forgetful transformation is the bundled
forgetful morphism. -/
@[simp]
theorem app (X : StackOver.Setoids.{u, v, max w vS, vS} J) :
    (forget.strongTrans J).app X = StackOver.Setoids.inertia.forget X := sorry

/-- The naturality isomorphism of setoid-stack inertia forgetting is the full-subbicategory lift
of the groupoid-stack naturality isomorphism. -/
@[simp]
theorem naturality
    {X Y : StackOver.Setoids.{u, v, max w vS, vS} J} (F : X ⟶ Y) :
    (forget.strongTrans J).naturality F =
      Bicategory.InducedBicategory.isoMk
        ((StackOver.Groupoids.Inertia.forget.strongTrans J).naturality
          (StackOver.Setoids.Hom.toGroupoidsMor F)) := sorry

/-- The ambient forward cell of setoid-stack inertia forgetful naturality is the corresponding
groupoid-stack cell. -/
@[simp]
theorem naturality.hom.toAmbient
    {X Y : StackOver.Setoids.{u, v, max w vS, vS} J} (F : X ⟶ Y) :
    ((forget.strongTrans J).naturality F).hom.hom =
      ((StackOver.Groupoids.Inertia.forget.strongTrans J).naturality
        (StackOver.Setoids.Hom.toGroupoidsMor F)).hom := sorry

/-- The ambient inverse cell of setoid-stack inertia forgetful naturality is the corresponding
groupoid-stack cell. -/
@[simp]
theorem naturality.inv.toAmbient
    {X Y : StackOver.Setoids.{u, v, max w vS, vS} J} (F : X ⟶ Y) :
    ((forget.strongTrans J).naturality F).inv.hom =
      ((StackOver.Groupoids.Inertia.forget.strongTrans J).naturality
        (StackOver.Setoids.Hom.toGroupoidsMor F)).inv := sorry

end forget.strongTrans

/-- The identity-automorphism section is a strong transformation from the identity
pseudofunctor to setoid-stack inertia. -/
@[stacks 04Z3 "setoid-stack inertia identity-section strong transformation"]
def identitySection.strongTrans :
    Pseudofunctor.StrongTrans
      (Pseudofunctor.id
        (StackOver.Setoids.{u, v, max w vS, vS} J))
      ((pseudofunctor J) :
        Pseudofunctor
          (StackOver.Setoids.{u, v, max w vS, vS} J)
          (StackOver.Setoids.{u, v, max w vS, vS} J)) :=
  ObjectProperty.FullSubbicategory.StrongTrans.fromId
    (P := IsStack.InSetoids.objectProperty J)
    (StackOver.Groupoids.Inertia.strictPseudofunctor J)
    (map_mem J)
    (StackOver.Groupoids.Inertia.identitySection.strongTrans J)

namespace identitySection.strongTrans

/-- The component of the setoid-stack inertia identity-section transformation is the bundled
identity section. -/
@[simp]
theorem app (X : StackOver.Setoids.{u, v, max w vS, vS} J) :
    (identitySection.strongTrans J).app X =
      StackOver.Setoids.inertia.identitySection X := sorry

/-- Forgetting the outer full-subbicategory layer sends setoid-stack identity-section
naturality to groupoid-stack identity-section naturality. -/
@[simp]
theorem naturality.toAmbient
    {X Y : StackOver.Setoids.{u, v, max w vS, vS} J} (F : X ⟶ Y) :
    Bicategory.InducedBicategory.Iso.toAmbient
        ((identitySection.strongTrans J).naturality F) =
      (StackOver.Groupoids.Inertia.identitySection.strongTrans J).naturality
        (StackOver.Setoids.Hom.toGroupoidsMor F) := sorry

/-- The ambient forward cell of setoid-stack identity-section naturality is the corresponding
groupoid-stack cell. -/
@[simp]
theorem naturality.hom.toAmbient
    {X Y : StackOver.Setoids.{u, v, max w vS, vS} J} (F : X ⟶ Y) :
    ((identitySection.strongTrans J).naturality F).hom.hom =
      ((StackOver.Groupoids.Inertia.identitySection.strongTrans J).naturality
        (StackOver.Setoids.Hom.toGroupoidsMor F)).hom := sorry

/-- The ambient inverse cell of setoid-stack identity-section naturality is the corresponding
groupoid-stack cell. -/
@[simp]
theorem naturality.inv.toAmbient
    {X Y : StackOver.Setoids.{u, v, max w vS, vS} J} (F : X ⟶ Y) :
    ((identitySection.strongTrans J).naturality F).inv.hom =
      ((StackOver.Groupoids.Inertia.identitySection.strongTrans J).naturality
        (StackOver.Setoids.Hom.toGroupoidsMor F)).inv := sorry

end identitySection.strongTrans

end StackOver.Setoids.Inertia

end CategoryTheory
