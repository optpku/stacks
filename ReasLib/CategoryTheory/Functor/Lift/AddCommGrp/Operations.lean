/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes
public import ReasLib.CategoryTheory.Functor.Lift.AddCommGrp

/-!
# Operation presentations of additive commutative group functor lifts

This module records the usual `0`, `-`, and `+` presentations of an additive commutative group
structure on a fixed type-valued functor.  Each presentation is equivalent to a lift through
`forget AddCommGrpCat`; no site or sheaf structure is involved.
-/

@[expose] public section

open CategoryTheory

universe w u v

/-- Natural `0`, `-`, and `+` operations on a type-valued functor satisfying the additive
commutative group axioms pointwise. -/
structure CompatibleAddCommGroupMaps {C : Type u} [Category.{w} C] (F : C ⥤ Type v) where
  /-- The zero section as a map from the singleton-valued functor. -/
  zero : ((Functor.const C).obj (PUnit : Type v) : C ⥤ Type v) ⟶ F
  /-- The additive inverse map. -/
  neg : F ⟶ F
  /-- The addition map. -/
  add : F ⨯ F ⟶ F
  /-- Zero is a left identity on every value of the functor. -/
  zero_add (c : C) (x : F.obj c) :
    add.app c (FunctorToTypes.prodMk (zero.app c PUnit.unit) x) = x
  /-- Zero is a right identity on every value of the functor. -/
  add_zero (c : C) (x : F.obj c) :
    add.app c (FunctorToTypes.prodMk x (zero.app c PUnit.unit)) = x
  /-- Addition is associative on every value of the functor. -/
  add_assoc (c : C) (x y z : F.obj c) :
    add.app c (FunctorToTypes.prodMk (add.app c (FunctorToTypes.prodMk x y)) z) =
      add.app c (FunctorToTypes.prodMk x (add.app c (FunctorToTypes.prodMk y z)))
  /-- Every section has a left additive inverse. -/
  add_left_neg (c : C) (x : F.obj c) :
    add.app c (FunctorToTypes.prodMk (neg.app c x) x) = zero.app c PUnit.unit
  /-- Addition is commutative on every value of the functor. -/
  add_comm (c : C) (x y : F.obj c) :
    add.app c (FunctorToTypes.prodMk x y) = add.app c (FunctorToTypes.prodMk y x)

/-- Natural `0`, `-`, and `+` operations together with the pointwise additive commutative groups
that they define. -/
structure CompatibleAddCommGroupMapStructure {C : Type u} [Category.{w} C]
    (F : C ⥤ Type v) where
  /-- The zero section as a map from the singleton-valued functor. -/
  zero : ((Functor.const C).obj (PUnit : Type v) : C ⥤ Type v) ⟶ F
  /-- The additive inverse map. -/
  neg : F ⟶ F
  /-- The addition map. -/
  add : F ⨯ F ⟶ F
  /-- The pointwise additive commutative group structures. -/
  addCommGroup (c : C) : AddCommGroup (F.obj c)
  /-- The zero map agrees with the pointwise zero. -/
  zero_eq (c : C) : zero.app c PUnit.unit = (addCommGroup c).zero
  /-- The inverse map agrees with the pointwise additive inverse. -/
  neg_eq (c : C) (x : F.obj c) : neg.app c x = (addCommGroup c).neg x
  /-- The addition map agrees with pointwise addition. -/
  add_eq (c : C) (x y : F.obj c) :
    add.app c (FunctorToTypes.prodMk x y) = (addCommGroup c).add x y

/-- An addition map together with the pointwise additive commutative groups it defines. -/
structure CompatibleAdditionMapStructure {C : Type u} [Category.{w} C] (F : C ⥤ Type v) where
  /-- The addition map. -/
  add : F ⨯ F ⟶ F
  /-- The pointwise additive commutative group structures. -/
  addCommGroup (c : C) : AddCommGroup (F.obj c)
  /-- The addition map agrees with pointwise addition. -/
  add_eq (c : C) (x y : F.obj c) :
    add.app c (FunctorToTypes.prodMk x y) = (addCommGroup c).add x y

namespace CategoryTheory.FunctorToTypes

variable {C : Type u} [Category.{w} C] {F G : C ⥤ Type v}

/-- The canonical product comparison sends `prodMk x y` to `(x, y)`. -/
@[simp]
theorem binaryProductIso_hom_app_prodMk (c : C) (x : F.obj c) (y : G.obj c) :
    (binaryProductIso F G).hom.app c (prodMk x y) = (x, y) := sorry

end CategoryTheory.FunctorToTypes

namespace CompatibleAddCommGroupStructure

variable {C : Type u} [Category.{w} C] {F : C ⥤ Type v}

/-- The zero natural transformation determined by a compatible pointwise group structure. -/
def zeroNatTrans (hF : CompatibleAddCommGroupStructure F) :
    ((Functor.const C).obj (PUnit : Type v) : C ⥤ Type v) ⟶ F where
  app c := ↾fun _ => (hF.addCommGroup c).zero
  naturality := sorry

/-- The negation natural transformation determined by a compatible pointwise group structure. -/
def negNatTrans (hF : CompatibleAddCommGroupStructure F) : F ⟶ F where
  app c := ↾(hF.addCommGroup c).neg
  naturality := sorry

/-- The addition natural transformation on the explicit pointwise product functor. -/
def addNatTrans (hF : CompatibleAddCommGroupStructure F) :
    FunctorToTypes.prod F F ⟶ F where
  app c := ↾fun z => (hF.addCommGroup c).add z.1 z.2
  naturality := sorry

/-- The pointwise-axiom presentation determined by compatible pointwise groups. -/
noncomputable def toCompatibleAddCommGroupMaps (hF : CompatibleAddCommGroupStructure F) :
    CompatibleAddCommGroupMaps F where
  zero := hF.zeroNatTrans
  neg := hF.negNatTrans
  add := (FunctorToTypes.binaryProductIso F F).hom ≫ hF.addNatTrans
  zero_add := sorry
  add_zero := sorry
  add_assoc := sorry
  add_left_neg := sorry
  add_comm := sorry

/-- The map-and-structure presentation determined by compatible pointwise groups. -/
noncomputable def toCompatibleAddCommGroupMapStructure
    (hF : CompatibleAddCommGroupStructure F) : CompatibleAddCommGroupMapStructure F where
  zero := hF.zeroNatTrans
  neg := hF.negNatTrans
  add := (FunctorToTypes.binaryProductIso F F).hom ≫ hF.addNatTrans
  addCommGroup := hF.addCommGroup
  zero_eq := sorry
  neg_eq := sorry
  add_eq := sorry

/-- The addition-first presentation determined by compatible pointwise groups. -/
noncomputable def toCompatibleAdditionMapStructure
    (hF : CompatibleAddCommGroupStructure F) : CompatibleAdditionMapStructure F where
  add := (FunctorToTypes.binaryProductIso F F).hom ≫ hF.addNatTrans
  addCommGroup := hF.addCommGroup
  add_eq := sorry

end CompatibleAddCommGroupStructure

namespace CompatibleAddCommGroupMaps

variable {C : Type u} [Category.{w} C] {F : C ⥤ Type v}

/-- The map-and-structure presentation induced by pointwise additive group axioms. -/
noncomputable def toCompatibleAddCommGroupMapStructure (hF : CompatibleAddCommGroupMaps F) :
    CompatibleAddCommGroupMapStructure F where
  zero := hF.zero
  neg := hF.neg
  add := hF.add
  addCommGroup c :=
    let _ : Zero (F.obj c) := ⟨hF.zero.app c PUnit.unit⟩
    let _ : Add (F.obj c) := ⟨fun x y => hF.add.app c (FunctorToTypes.prodMk x y)⟩
    let _ : Neg (F.obj c) := ⟨hF.neg.app c⟩
    { AddGroup.ofLeftAxioms (hF.add_assoc c) (hF.zero_add c) (hF.add_left_neg c) with
      add_comm := hF.add_comm c }
  zero_eq := sorry
  neg_eq := sorry
  add_eq := sorry

/-- The compatible pointwise groups induced by pointwise additive group axioms. -/
noncomputable def toCompatibleAddCommGroupStructure (hF : CompatibleAddCommGroupMaps F) :
    CompatibleAddCommGroupStructure F where
  addCommGroup := hF.toCompatibleAddCommGroupMapStructure.addCommGroup
  map_add := sorry

end CompatibleAddCommGroupMaps

namespace CompatibleAddCommGroupMapStructure

variable {C : Type u} [Category.{w} C] {F : C ⥤ Type v}

/-- The compatible pointwise groups obtained from the map-and-structure presentation. -/
def toCompatibleAddCommGroupStructure (hF : CompatibleAddCommGroupMapStructure F) :
    CompatibleAddCommGroupStructure F where
  addCommGroup := hF.addCommGroup
  map_add := sorry

end CompatibleAddCommGroupMapStructure

namespace CompatibleAdditionMapStructure

variable {C : Type u} [Category.{w} C] {F : C ⥤ Type v}

/-- The addition map agrees pointwise with the chosen pointwise addition. -/
theorem add_app_eq_add (hF : CompatibleAdditionMapStructure F) (c : C)
    (x y : F.obj c) :
    hF.add.app c (FunctorToTypes.prodMk x y) = (hF.addCommGroup c).add x y := sorry

/-- The compatible pointwise groups obtained from the addition-first presentation. -/
def toCompatibleAddCommGroupStructure (hF : CompatibleAdditionMapStructure F) :
    CompatibleAddCommGroupStructure F where
  addCommGroup := hF.addCommGroup
  map_add := sorry

end CompatibleAdditionMapStructure

namespace CompatibleAddCommGroupMaps

/-- Pointwise `0`, `-`, and `+` axioms on a fixed type-valued functor are equivalent to lifts
through `forget AddCommGrpCat`. -/
@[stacks 006J "pointwise operations and additive-group-valued lifts"]
noncomputable def equivAddCommGrpCatLift
  {C : Type u} [Category.{w} C] (F : C ⥤ Type v) :
    CompatibleAddCommGroupMaps F ≃
      { G : C ⥤ AddCommGrpCat.{v} // G ⋙ forget AddCommGrpCat = F } where
  toFun hF :=
    CompatibleAddCommGroupStructure.equivAddCommGrpCatLift F
      hF.toCompatibleAddCommGroupStructure
  invFun hG :=
    (CompatibleAddCommGroupStructure.equivAddCommGrpCatLift F).symm hG
      |>.toCompatibleAddCommGroupMaps
  left_inv := sorry
  right_inv := sorry

end CompatibleAddCommGroupMaps

namespace CompatibleAddCommGroupMapStructure

/-- A `0`, `-`, and `+` presentation with its pointwise groups is equivalent to lifts through
`forget AddCommGrpCat`. -/
@[stacks 006J "operation structures and additive-group-valued lifts"]
noncomputable def equivAddCommGrpCatLift
  {C : Type u} [Category.{w} C] (F : C ⥤ Type v) :
    CompatibleAddCommGroupMapStructure F ≃
      { G : C ⥤ AddCommGrpCat.{v} // G ⋙ forget AddCommGrpCat = F } where
  toFun hF :=
    CompatibleAddCommGroupStructure.equivAddCommGrpCatLift F
      hF.toCompatibleAddCommGroupStructure
  invFun hG :=
    (CompatibleAddCommGroupStructure.equivAddCommGrpCatLift F).symm hG
      |>.toCompatibleAddCommGroupMapStructure
  left_inv := sorry
  right_inv := sorry

end CompatibleAddCommGroupMapStructure

namespace CompatibleAdditionMapStructure

/-- An addition-first presentation with pointwise groups is equivalent to lifts through
`forget AddCommGrpCat`. -/
@[stacks 006J "addition presentations and additive-group-valued lifts"]
noncomputable def equivAddCommGrpCatLift
  {C : Type u} [Category.{w} C] (F : C ⥤ Type v) :
    CompatibleAdditionMapStructure F ≃
      { G : C ⥤ AddCommGrpCat.{v} // G ⋙ forget AddCommGrpCat = F } where
  toFun hF :=
    CompatibleAddCommGroupStructure.equivAddCommGrpCatLift F
      hF.toCompatibleAddCommGroupStructure
  invFun hG :=
    (CompatibleAddCommGroupStructure.equivAddCommGrpCatLift F).symm hG
      |>.toCompatibleAdditionMapStructure
  left_inv := sorry
  right_inv := sorry

end CompatibleAdditionMapStructure
