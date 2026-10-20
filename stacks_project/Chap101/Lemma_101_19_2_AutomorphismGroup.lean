/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.AutomorphismGroup

/-!
# Automorphism group algebraic spaces of field-valued points

The field-valued automorphism constructions and their ground-field-invariant
properties are provided by the shared mathematical owner.
-/

open CategoryTheory AlgebraicGeometry
open Bicategory FiberedCategoryOver.Groupoids CategoryTheory.Limits
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

#check (AlgebraicGeometry.AlgebraicStack.FieldValuedPoint.toHom :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} (p : FieldValuedPoint X),
    (AlgebraicSpace.ofOver p.overObj).toGroupoids ⟶ X)

#check (AlgebraicGeometry.AlgebraicStack.FieldValuedPoint.toHom_eq :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
    (p : FieldValuedPoint X),
    p.toHom = (AlgebraicSpace.ofOverSliceEquiv p.overObj).hom ≫ p.hom)

#check (AlgebraicGeometry.AlgebraicStack.automorphismGroup :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
    (p : FieldValuedPoint X),
    GroupoidsOver S)

#check (AlgebraicGeometry.AlgebraicStack.automorphismGroup_eq :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
    (p : FieldValuedPoint X),
    automorphismGroup p = isomApex p.toHom p.toHom)

#check (AlgebraicGeometry.AlgebraicStack.automorphismGroup.structureHom :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
    (p : FieldValuedPoint X),
    automorphismGroup p ⟶ (AlgebraicSpace.ofOver p.overObj).toGroupoids)

#check (AlgebraicGeometry.AlgebraicStack.automorphismGroup.structureHom_eq :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
    (p : FieldValuedPoint X),
    automorphismGroup.structureHom p =
      TwoFibreProduct.fst.{u + 1, u, u + 1, u}
        (diagonal.{u + 1, u, u + 1}
          (AlgebraicSpace.ofOver p.overObj).toGroupoids)
        (toSelfProduct p.toHom p.toHom))

#check (AlgebraicGeometry.AlgebraicStack.automorphismGroup.Has :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (P : MorphismProperty (AlgebraicSpace S)) (p : FieldValuedPoint X),
    Prop)

#check (AlgebraicGeometry.AlgebraicStack.automorphismGroup.Has_iff :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (P : MorphismProperty (AlgebraicSpace S)) (p : FieldValuedPoint X),
    automorphismGroup.Has P p ↔
      ∀ (G : AlgebraicSpace S) (g : G ⟶ AlgebraicSpace.ofOver p.overObj),
        RepresentsBaseChange (automorphismGroup.structureHom p)
          (AlgebraicSpace.ofOverSliceEquiv p.overObj).inv G g → P g)

#check (AlgebraicGeometry.AlgebraicStack.IsInvariantUnderGroundFieldExtension :
    ∀ {S : Scheme.{u}} (P : MorphismProperty (AlgebraicSpace S)), Prop)

#check (AlgebraicGeometry.AlgebraicStack.IsInvariantUnderGroundFieldExtension.iff :
    ∀ {S : Scheme.{u}}
    {P : MorphismProperty (AlgebraicSpace S)}
    [IsInvariantUnderGroundFieldExtension P] {k K : Type u} [Field k]
    [Field K] [Algebra k K] {σk : Spec (.of k) ⟶ S}
    {σK : Spec (.of K) ⟶ S} (hσ : FieldExtension.specMap k K ≫ σk = σK)
    {X XK : AlgebraicSpace S} {f : X ⟶ AlgebraicSpace.ofOver (Over.mk σk)}
    {g : XK ⟶ AlgebraicSpace.ofOver (Over.mk σK)} {h : XK ⟶ X}
    (sq : IsPullback g h
      (AlgebraicSpace.ofOverHomMk (FieldExtension.specMap k K) hσ) f),
    P f ↔ P g)

#check (AlgebraicGeometry.AlgebraicStack.isFinite_isInvariantUnderGroundFieldExtension :
    ∀ {S : Scheme.{u}},
    IsInvariantUnderGroundFieldExtension (@AlgebraicSpace.IsFinite S))

end AlgebraicGeometry.AlgebraicStack
