module

public import Mathlib.Algebra.Group.MinimalAxioms
public import Mathlib.Algebra.Category.Grp.Basic

/-!
# Lifting type-valued functors to additive commutative groups

This file packages compatible additive commutative group structures on the values of a
type-valued functor and their associated lift through the forgetful functor from
`AddCommGrpCat`.
-/

@[expose] public section

open CategoryTheory

universe w u v

/-- Additive commutative group structures on the values of a `Type`-valued functor for which
every functorial map is additive. -/
structure CompatibleAddCommGroupStructure {C : Type u} [Category.{w} C]
    (F : C ⥤ Type v) where
  /-- The additive commutative group structure on the value at an object. -/
  addCommGroup (c : C) : AddCommGroup (F.obj c)
  /-- Every map of the functor preserves addition. -/
  map_add {c d : C} (f : c ⟶ d) (x y : F.obj c) :
    F.map f ((addCommGroup c).add x y) =
      (addCommGroup d).add (F.map f x) (F.map f y)

namespace CompatibleAddCommGroupStructure

variable {C : Type u} [Category.{w} C] {F : C ⥤ Type v}

/-- The additive commutative group attached to one value of a compatible pointwise structure. -/
def toAddCommGrpCatObj (hF : CompatibleAddCommGroupStructure F) (c : C) :
    AddCommGrpCat.{v} :=
  @AddCommGrpCat.of (F.obj c) (hF.addCommGroup c)

/-- A functorial map, regarded as a homomorphism between the compatible pointwise additive
commutative groups. -/
def toAddCommGrpCatMap (hF : CompatibleAddCommGroupStructure F) {c d : C} (f : c ⟶ d) :
    hF.toAddCommGrpCatObj c ⟶ hF.toAddCommGrpCatObj d :=
  @AddCommGrpCat.ofHom (F.obj c) (F.obj d) (hF.addCommGroup c) (hF.addCommGroup d) <|
    @AddMonoidHom.mk' (F.obj c) (F.obj d) (hF.addCommGroup d).toAddGroup
      (hF.addCommGroup c).toAddZeroClass (F.map f) (hF.map_add f)

/-- Lift a compatible family of additive commutative group structures to an
`AddCommGrpCat`-valued functor. -/
noncomputable def toAddCommGrpCat (hF : CompatibleAddCommGroupStructure F) :
    C ⥤ AddCommGrpCat.{v} where
  obj := hF.toAddCommGrpCatObj
  map := hF.toAddCommGrpCatMap
  map_id := sorry
  map_comp := sorry

/-- Forgetting the canonical `AddCommGrpCat`-valued lift recovers the original functor. -/
theorem toAddCommGrpCat_forget (hF : CompatibleAddCommGroupStructure F) :
    hF.toAddCommGrpCat ⋙ forget AddCommGrpCat = F := sorry

/-- The compatible pointwise group structures underlying an `AddCommGrpCat`-valued functor. -/
def ofAddCommGrpCat (G : C ⥤ AddCommGrpCat.{v}) :
    CompatibleAddCommGroupStructure (G ⋙ forget AddCommGrpCat) where
  addCommGroup c := (G.obj c).str
  map_add := sorry

/-- Compatible pointwise additive commutative group structures on `F` are equivalent to
`AddCommGrpCat`-valued lifts with underlying functor exactly `F`. -/
@[stacks 006J "compatible pointwise groups and additive-group-valued lifts"]
noncomputable def equivAddCommGrpCatLift
    {C : Type u} [Category.{w} C] (F : C ⥤ Type v) :
    CompatibleAddCommGroupStructure F ≃
      { G : C ⥤ AddCommGrpCat.{v} // G ⋙ forget AddCommGrpCat = F } where
  toFun hF := ⟨hF.toAddCommGrpCat, hF.toAddCommGrpCat_forget⟩
  invFun hG := hG.2 ▸ CompatibleAddCommGroupStructure.ofAddCommGrpCat hG.1
  left_inv := sorry
  right_inv := sorry

end CompatibleAddCommGroupStructure
