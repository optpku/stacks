module

public import Mathlib.CategoryTheory.Preadditive.Opposite
public import ReasLib.Algebra.Module.CharacterModule
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# The character-module functor

For a commutative ring, character duality is a contravariant endofunctor on
modules. For an arbitrary ring, the natural target consists of modules over
the opposite ring.
-/

open CategoryTheory

universe u v

namespace CharacterModule

section Commutative

variable (R : Type u) [CommRing R]

/-- A character module, bundled as an `R`-module. -/
@[stacks 01D9 "commutative character-module object"]
abbrev moduleObj (M : ModuleCat.{v} R) : ModuleCat.{v} R :=
  ModuleCat.of R (CharacterModule M)

/-- Precomposition as a morphism between bundled character modules. -/
@[stacks 01D9 "commutative character-module dual map"]
def dualMap {M N : ModuleCat.{v} R} (f : M ⟶ N) :
    moduleObj R N ⟶ moduleObj R M :=
  ModuleCat.ofHom (CharacterModule.dual f.hom)

/-- Bundled character dualization is precomposition on elements. -/
@[simp]
theorem dualMap_apply {M N : ModuleCat.{v} R} (f : M ⟶ N)
    (χ : CharacterModule N) (m : M) : dualMap R f χ m = χ (f m) := sorry
/- Proof strategy: unfold `dualMap` and use
`CharacterModule.dual_apply`. -/

/-- Bundled character dualization preserves identity maps. -/
@[simp]
theorem dualMap_id (M : ModuleCat.{v} R) :
    dualMap R (𝟙 M) = 𝟙 (moduleObj R M) := sorry
/- Proof strategy: extensionality on a character and a module element, then
use `dualMap_apply`. -/

/-- Bundled character dualization reverses composition. -/
theorem dualMap_comp {M N P : ModuleCat.{v} R}
    (f : M ⟶ N) (g : N ⟶ P) :
    dualMap R (f ≫ g) = dualMap R g ≫ dualMap R f := sorry
/- Proof strategy: extensionality and `dualMap_apply`. -/

/-- Bundled character dualization preserves addition of morphisms. -/
theorem dualMap_add {M N : ModuleCat.{v} R} (f g : M ⟶ N) :
    dualMap R (f + g) = dualMap R f + dualMap R g := sorry
/- Proof strategy: extensionality and additivity of each character. -/

/-- Character modules form a contravariant endofunctor on modules over a
commutative ring. -/
@[stacks 01D9 "contravariant character-module functor"]
def functor : (ModuleCat.{v} R)ᵒᵖ ⥤ ModuleCat.{v} R where
  obj M := moduleObj R M.unop
  map f := dualMap R f.unop
  map_id M := dualMap_id R M.unop
  map_comp f g := dualMap_comp R g.unop f.unop

/-- The commutative character-module functor acts by the bundled dual map. -/
@[simp]
theorem functor_map_op {M N : ModuleCat.{v} R} (f : M ⟶ N) :
    (functor R).map f.op = dualMap R f := sorry
/- Proof strategy: unfold `functor`; the two maps are definitionally equal. -/

/-- The commutative character-module functor preserves addition of
morphisms. -/
theorem functor_map_add {M N : (ModuleCat.{v} R)ᵒᵖ} (f g : M ⟶ N) :
    (functor R).map (f + g) = (functor R).map f + (functor R).map g := sorry
/- Proof strategy: unfold `functor`, rewrite opposite addition, and apply
`dualMap_add`. -/

/-- Character duality is an additive functor. -/
@[stacks 01D9 "additivity of character duality"]
instance instFunctorAdditive : (functor R).Additive where
  map_add := fun {X Y f g} ↦ functor_map_add R (M := X) (N := Y) f g

end Commutative

section Opposite

variable (R : Type u) [Ring R]

/-- A character module, bundled over the opposite ring. -/
@[stacks 01D9 "opposite-ring character-module object"]
abbrev oppositeObj (M : ModuleCat.{v} R) : ModuleCat.{v} Rᵐᵒᵖ :=
  ModuleCat.of Rᵐᵒᵖ (CharacterModule M)

/-- Opposite-linear precomposition between bundled character modules. -/
@[stacks 01D9 "opposite-ring character-module dual map"]
def dualOppositeMap {M N : ModuleCat.{v} R} (f : M ⟶ N) :
    oppositeObj R N ⟶ oppositeObj R M :=
  ModuleCat.ofHom (CharacterModule.dualOpposite f.hom)

/-- Bundled opposite-linear character dualization is precomposition on
elements. -/
@[simp]
theorem dualOppositeMap_apply {M N : ModuleCat.{v} R} (f : M ⟶ N)
    (χ : CharacterModule N) (m : M) :
    dualOppositeMap R f χ m = χ (f m) := sorry
/- Proof strategy: unfold `dualOppositeMap` and apply
`CharacterModule.dualOpposite_apply`. -/

/-- Bundled opposite-linear character dualization preserves identities. -/
@[simp]
theorem dualOppositeMap_id (M : ModuleCat.{v} R) :
    dualOppositeMap R (𝟙 M) = 𝟙 (oppositeObj R M) := sorry
/- Proof strategy: apply `ModuleCat.hom_ext` and
`CharacterModule.dualOpposite_id`. -/

/-- Bundled opposite-linear character dualization reverses composition. -/
theorem dualOppositeMap_comp {M N P : ModuleCat.{v} R}
    (f : M ⟶ N) (g : N ⟶ P) :
    dualOppositeMap R (f ≫ g) =
      dualOppositeMap R g ≫ dualOppositeMap R f := sorry
/- Proof strategy: apply `ModuleCat.hom_ext` and
`CharacterModule.dualOpposite_comp`. -/

/-- Bundled opposite-linear character dualization preserves addition. -/
theorem dualOppositeMap_add {M N : ModuleCat.{v} R} (f g : M ⟶ N) :
    dualOppositeMap R (f + g) =
      dualOppositeMap R f + dualOppositeMap R g := sorry
/- Proof strategy: extensionality and pointwise additivity of characters. -/

/-- Character duality sends left `R`-modules contravariantly to left
`Rᵐᵒᵖ`-modules. -/
@[stacks 01D9 "noncommutative character-module functor"]
def opFunctor : (ModuleCat.{v} R)ᵒᵖ ⥤ ModuleCat.{v} Rᵐᵒᵖ where
  obj M := oppositeObj R M.unop
  map f := dualOppositeMap R f.unop
  map_id M := dualOppositeMap_id R M.unop
  map_comp f g := dualOppositeMap_comp R g.unop f.unop

/-- The noncommutative character-module functor acts by the bundled
opposite-linear dual map. -/
@[simp]
theorem opFunctor_map_op {M N : ModuleCat.{v} R} (f : M ⟶ N) :
    (opFunctor R).map f.op = dualOppositeMap R f := sorry
/- Proof strategy: unfold `opFunctor`; the two maps are definitionally
equal. -/

/-- The noncommutative character-module functor preserves addition. -/
theorem opFunctor_map_add {M N : (ModuleCat.{v} R)ᵒᵖ} (f g : M ⟶ N) :
    (opFunctor R).map (f + g) =
      (opFunctor R).map f + (opFunctor R).map g := sorry
/- Proof strategy: unfold `opFunctor`, rewrite opposite addition, and apply
`dualOppositeMap_add`. -/

/-- Noncommutative character duality is an additive functor. -/
@[stacks 01D9 "additivity of opposite-ring character duality"]
instance instOpFunctorAdditive : (opFunctor R).Additive where
  map_add := fun {X Y f g} ↦ opFunctor_map_add R (M := X) (N := Y) f g

end Opposite

end CharacterModule
