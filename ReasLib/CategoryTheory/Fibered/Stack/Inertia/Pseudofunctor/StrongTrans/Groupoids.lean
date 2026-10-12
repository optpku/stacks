/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.StrongTrans
public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.AbsoluteTransformations.StrongTrans
public import ReasLib.CategoryTheory.Fibered.Stack.Inertia.Pseudofunctor.Computations.Groupoids

/-!
# Strong inertia transformations on stacks in groupoids

The groupoid-stack forgetful morphism and identity section, assembled as transformations of
the absolute-inertia pseudofunctor.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace StackOver.Groupoids.Inertia

variable (J : GrothendieckTopology C)

/-- Forgetting the selected automorphism is a strong transformation from groupoid-stack inertia
to the identity pseudofunctor. -/
@[stacks 042H "groupoid-stack inertia forgetful strong transformation"]
def forget.strongTrans :
    Pseudofunctor.StrongTrans
      ((pseudofunctor J) :
        Pseudofunctor
          (StackOver.Groupoids.{u, v, max w vS, vS} J)
          (StackOver.Groupoids.{u, v, max w vS, vS} J))
      (Pseudofunctor.id
        (StackOver.Groupoids.{u, v, max w vS, vS} J)) :=
  ObjectProperty.FullSubbicategory.StrongTrans.toId
    (FiberedCategoryOver.Groupoids.Inertia.strictPseudofunctor C)
    (map_mem J)
    (FiberedCategoryOver.Groupoids.Inertia.forget.strongTrans C)

namespace forget.strongTrans

/-- The component of the groupoid-stack inertia forgetful transformation is the bundled
forgetful morphism. -/
@[simp]
theorem app (X : StackOver.Groupoids.{u, v, max w vS, vS} J) :
    (forget.strongTrans J).app X = StackOver.Groupoids.inertia.forget X := sorry

/-- The naturality isomorphism of groupoid-stack inertia forgetting is the full-subbicategory
lift of the groupoid-fibred naturality isomorphism. -/
@[simp]
theorem naturality
    {X Y : StackOver.Groupoids.{u, v, max w vS, vS} J} (F : X ⟶ Y) :
    (forget.strongTrans J).naturality F =
      Bicategory.InducedBicategory.isoMk
        ((FiberedCategoryOver.Groupoids.Inertia.forget.strongTrans C).naturality
          (StackOver.Groupoids.Hom.toGroupoidsMor F)) := sorry

/-- The ambient forward cell of groupoid-stack inertia forgetful naturality is the
corresponding groupoid-fibred cell. -/
@[simp]
theorem naturality.hom.toAmbient
    {X Y : StackOver.Groupoids.{u, v, max w vS, vS} J} (F : X ⟶ Y) :
    ((forget.strongTrans J).naturality F).hom.hom =
      ((FiberedCategoryOver.Groupoids.Inertia.forget.strongTrans C).naturality
        (StackOver.Groupoids.Hom.toGroupoidsMor F)).hom := sorry

/-- The ambient inverse cell of groupoid-stack inertia forgetful naturality is the
corresponding groupoid-fibred cell. -/
@[simp]
theorem naturality.inv.toAmbient
    {X Y : StackOver.Groupoids.{u, v, max w vS, vS} J} (F : X ⟶ Y) :
    ((forget.strongTrans J).naturality F).inv.hom =
      ((FiberedCategoryOver.Groupoids.Inertia.forget.strongTrans C).naturality
        (StackOver.Groupoids.Hom.toGroupoidsMor F)).inv := sorry

end forget.strongTrans

/-- The identity-automorphism section is a strong transformation from the identity
pseudofunctor to groupoid-stack inertia. -/
@[stacks 04Z3 "groupoid-stack inertia identity-section strong transformation"]
def identitySection.strongTrans :
    Pseudofunctor.StrongTrans
      (Pseudofunctor.id
        (StackOver.Groupoids.{u, v, max w vS, vS} J))
      ((pseudofunctor J) :
        Pseudofunctor
          (StackOver.Groupoids.{u, v, max w vS, vS} J)
          (StackOver.Groupoids.{u, v, max w vS, vS} J)) :=
  ObjectProperty.FullSubbicategory.StrongTrans.fromId
    (FiberedCategoryOver.Groupoids.Inertia.strictPseudofunctor C)
    (map_mem J)
    (FiberedCategoryOver.Groupoids.Inertia.identitySection.strongTrans C)

namespace identitySection.strongTrans

/-- The component of the groupoid-stack inertia identity-section transformation is the bundled
identity section. -/
@[simp]
theorem app (X : StackOver.Groupoids.{u, v, max w vS, vS} J) :
    (identitySection.strongTrans J).app X =
      StackOver.Groupoids.inertia.identitySection X := sorry

/-- The naturality isomorphism of the groupoid-stack inertia identity section is the
full-subbicategory lift of the groupoid-fibred naturality isomorphism. -/
@[simp]
theorem naturality
    {X Y : StackOver.Groupoids.{u, v, max w vS, vS} J} (F : X ⟶ Y) :
    (identitySection.strongTrans J).naturality F =
      ObjectProperty.FullSubbicategory.StrongTrans.FromId.naturality
        (P := IsStack.InGroupoids.objectProperty J)
        (FiberedCategoryOver.Groupoids.Inertia.strictPseudofunctor C)
        (map_mem J)
        (FiberedCategoryOver.Groupoids.Inertia.identitySection.strongTrans C) F := sorry

/-- The ambient forward cell of groupoid-stack identity-section naturality is the
corresponding groupoid-fibred cell. -/
@[simp]
theorem naturality.hom.toAmbient
    {X Y : StackOver.Groupoids.{u, v, max w vS, vS} J} (F : X ⟶ Y) :
    ((identitySection.strongTrans J).naturality F).hom.hom =
      ((FiberedCategoryOver.Groupoids.Inertia.identitySection.strongTrans C).naturality
        (StackOver.Groupoids.Hom.toGroupoidsMor F)).hom := sorry

/-- The ambient inverse cell of groupoid-stack identity-section naturality is the
corresponding groupoid-fibred cell. -/
@[simp]
theorem naturality.inv.toAmbient
    {X Y : StackOver.Groupoids.{u, v, max w vS, vS} J} (F : X ⟶ Y) :
    ((identitySection.strongTrans J).naturality F).inv.hom =
      ((FiberedCategoryOver.Groupoids.Inertia.identitySection.strongTrans C).naturality
        (StackOver.Groupoids.Hom.toGroupoidsMor F)).inv := sorry

end identitySection.strongTrans

end StackOver.Groupoids.Inertia

end CategoryTheory
