module

public import Mathlib.Algebra.Module.CharacterModule
public import Mathlib.CategoryTheory.Preadditive.Opposite

/-!
# Character duality on additive commutative groups

This file bundles precomposition of additive characters as a contravariant functor on
additive commutative groups.
-/

@[expose] public section

open CategoryTheory

universe u

namespace CharacterModule

/-- Precomposition of characters, bundled as a morphism of additive commutative groups. -/
def dualAddMap {M N : AddCommGrpCat.{u}} (f : M ⟶ N) :
    AddCommGrpCat.of (CharacterModule N) ⟶ AddCommGrpCat.of (CharacterModule M) :=
  AddCommGrpCat.ofHom (CharacterModule.dual f.hom.toIntLinearMap).toAddMonoidHom

/-- Additive-group character dualization is evaluation by precomposition. -/
theorem dualAddMap_apply {M N : AddCommGrpCat.{u}} (f : M ⟶ N)
    (χ : CharacterModule N) (m : M) : dualAddMap f χ m = χ (f m) := sorry

/-- Additive-group character dualization preserves identity morphisms. -/
theorem dualAddMap_id (M : AddCommGrpCat.{u}) :
    dualAddMap (𝟙 M) = 𝟙 (AddCommGrpCat.of (CharacterModule M)) := sorry

/-- Additive-group character dualization reverses composition. -/
theorem dualAddMap_comp {M N P : AddCommGrpCat.{u}} (f : M ⟶ N) (g : N ⟶ P) :
    dualAddMap (f ≫ g) = dualAddMap g ≫ dualAddMap f := sorry

/-- Character duality as a contravariant functor on additive commutative groups. -/
def addCommGrpFunctor : AddCommGrpCat.{u}ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj M := AddCommGrpCat.of (CharacterModule M.unop)
  map f := dualAddMap f.unop
  map_id M := dualAddMap_id M.unop
  map_comp f g := dualAddMap_comp g.unop f.unop

/-- The additive-group character-duality functor acts by precomposition. -/
theorem addCommGrpFunctor_map_op {M N : AddCommGrpCat.{u}} (f : M ⟶ N) :
    addCommGrpFunctor.map f.op = dualAddMap f := sorry

end CharacterModule
