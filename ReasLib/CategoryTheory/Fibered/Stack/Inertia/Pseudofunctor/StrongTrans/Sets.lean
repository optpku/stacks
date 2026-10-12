/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.StrongTrans
public import ReasLib.CategoryTheory.Fibered.Stack.Inertia.Pseudofunctor.Computations.Sets
public import ReasLib.CategoryTheory.Fibered.Stack.Inertia.Pseudofunctor.StrongTrans.Setoids

/-!
# Strong inertia transformations on stacks in sets

The forgetful and identity-section strong transformations and the resulting equivalence between
set-stack inertia and the identity pseudofunctor.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open scoped Bicategory Pseudofunctor.StrongTrans

variable {C : Type u} [Category.{v} C]

namespace StackOver.Sets.Inertia

variable (J : GrothendieckTopology C)

/-- Forgetting the selected automorphism is a strong transformation from set-stack inertia to
the identity pseudofunctor. -/
@[stacks 042H "set-stack inertia forgetful strong transformation"]
def forget.strongTrans :
    Pseudofunctor.StrongTrans
      ((pseudofunctor J) :
        Pseudofunctor
          (StackOver.Sets.{u, v, max w vS, vS} J)
          (StackOver.Sets.{u, v, max w vS, vS} J))
      (Pseudofunctor.id
        (StackOver.Sets.{u, v, max w vS, vS} J)) :=
  ObjectProperty.FullSubbicategory.StrongTrans.toId
    (D := StackOver.Setoids.{u, v, max w vS, vS} J)
    (P := IsStack.InSets.objectProperty J)
    (StackOver.Setoids.Inertia.strictPseudofunctor J)
    (map_mem J)
    (StackOver.Setoids.Inertia.forget.strongTrans J)

namespace forget.strongTrans

/-- The component of set-stack inertia forgetting is the concrete forgetful morphism. -/
@[simp]
theorem app (X : StackOver.Sets.{u, v, max w vS, vS} J) :
    (forget.strongTrans J).app X = StackOver.Sets.inertia.forget X := sorry

/-- Forgetting the outer full-subbicategory layer sends set-stack forgetful naturality to
setoid-stack forgetful naturality. -/
@[simp]
theorem naturality.toAmbient
    {X Y : StackOver.Sets.{u, v, max w vS, vS} J} (F : X ⟶ Y) :
    Bicategory.InducedBicategory.Iso.toAmbient
        ((forget.strongTrans J).naturality F) =
      (StackOver.Setoids.Inertia.forget.strongTrans J).naturality
        (StackOver.Sets.Hom.toSetoidsMor F) := sorry

/-- The ambient forward cell of set-stack inertia forgetful naturality is the corresponding
setoid-stack cell. -/
@[simp]
theorem naturality.hom.toAmbient
    {X Y : StackOver.Sets.{u, v, max w vS, vS} J} (F : X ⟶ Y) :
    ((forget.strongTrans J).naturality F).hom.hom =
      ((StackOver.Setoids.Inertia.forget.strongTrans J).naturality
        (StackOver.Sets.Hom.toSetoidsMor F)).hom := sorry

/-- The ambient inverse cell of set-stack inertia forgetful naturality is the corresponding
setoid-stack cell. -/
@[simp]
theorem naturality.inv.toAmbient
    {X Y : StackOver.Sets.{u, v, max w vS, vS} J} (F : X ⟶ Y) :
    ((forget.strongTrans J).naturality F).inv.hom =
      ((StackOver.Setoids.Inertia.forget.strongTrans J).naturality
        (StackOver.Sets.Hom.toSetoidsMor F)).inv := sorry

end forget.strongTrans

/-- The identity-automorphism section is a strong transformation from the identity
pseudofunctor to set-stack inertia. -/
@[stacks 04Z3 "set-stack inertia identity-section strong transformation"]
def identitySection.strongTrans :
    Pseudofunctor.StrongTrans
      (Pseudofunctor.id
        (StackOver.Sets.{u, v, max w vS, vS} J))
      ((pseudofunctor J) :
        Pseudofunctor
          (StackOver.Sets.{u, v, max w vS, vS} J)
          (StackOver.Sets.{u, v, max w vS, vS} J)) :=
  ObjectProperty.FullSubbicategory.StrongTrans.fromId
    (D := StackOver.Setoids.{u, v, max w vS, vS} J)
    (P := IsStack.InSets.objectProperty J)
    (StackOver.Setoids.Inertia.strictPseudofunctor J)
    (map_mem J)
    (StackOver.Setoids.Inertia.identitySection.strongTrans J)

namespace identitySection.strongTrans

/-- The component of the identity-section strong transformation is the concrete identity
section. -/
@[simp]
theorem app (X : StackOver.Sets.{u, v, max w vS, vS} J) :
    (identitySection.strongTrans J).app X =
      StackOver.Sets.inertia.identitySection X := sorry

/-- Forgetting the outer full-subbicategory layer sends set-stack identity-section naturality
to setoid-stack identity-section naturality. -/
@[simp]
theorem naturality.toAmbient
    {X Y : StackOver.Sets.{u, v, max w vS, vS} J} (F : X ⟶ Y) :
    Bicategory.InducedBicategory.Iso.toAmbient
        ((identitySection.strongTrans J).naturality F) =
      (StackOver.Setoids.Inertia.identitySection.strongTrans J).naturality
        (StackOver.Sets.Hom.toSetoidsMor F) := sorry

/-- The ambient forward cell of set-stack identity-section naturality is the corresponding
setoid-stack cell. -/
@[simp]
theorem naturality.hom.toAmbient
    {X Y : StackOver.Sets.{u, v, max w vS, vS} J} (F : X ⟶ Y) :
    ((identitySection.strongTrans J).naturality F).hom.hom =
      ((StackOver.Setoids.Inertia.identitySection.strongTrans J).naturality
        (StackOver.Sets.Hom.toSetoidsMor F)).hom := sorry

/-- The ambient inverse cell of set-stack identity-section naturality is the corresponding
setoid-stack cell. -/
@[simp]
theorem naturality.inv.toAmbient
    {X Y : StackOver.Sets.{u, v, max w vS, vS} J} (F : X ⟶ Y) :
    ((identitySection.strongTrans J).naturality F).inv.hom =
      ((StackOver.Setoids.Inertia.identitySection.strongTrans J).naturality
        (StackOver.Sets.Hom.toSetoidsMor F)).inv := sorry

end identitySection.strongTrans

end StackOver.Sets.Inertia

end CategoryTheory
