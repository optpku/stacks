module

public import Mathlib.CategoryTheory.Monoidal.Bimod

/-!
# Functorial balanced tensor products of bimodules

Mathlib constructs the balanced tensor product of two bimodule objects as a coequalizer and
provides its action on a morphism in either variable.  This file packages those constructions as
functors.  The resulting API is independent of rings, graded objects, complexes, or sheaves and
can therefore be reused by every relative tensor-product construction built from bimodules.
-/

@[expose] public section

open CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory.Bimod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable [HasCoequalizers C]
variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft X)]
variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight X)]
variable {R S T : Mon C}

/-- Balanced tensor product with a fixed bimodule in the left variable. -/
@[stacks 0FSA "generic balanced tensor functor in the right bimodule"]
def tensorLeft (P : Bimod R S) : Bimod S T ⥤ Bimod R T where
  obj Q := P.tensorBimod Q
  map f := Bimod.whiskerLeft P f
  map_id := sorry
  map_comp := sorry

/-- Balanced tensor product with a fixed bimodule in the right variable. -/
@[stacks 0FSA "generic balanced tensor functor in the left bimodule"]
def tensorRight (Q : Bimod S T) : Bimod R S ⥤ Bimod R T where
  obj P := P.tensorBimod Q
  map f := Bimod.whiskerRight f Q
  map_id := sorry
  map_comp := sorry

/-- The underlying-object functor of balanced tensor product with a fixed left bimodule. -/
@[stacks 0FSA "underlying generic balanced tensor functor in the right bimodule"]
def tensorLeftUnderlying (P : Bimod R S) : Bimod S T ⥤ C :=
  tensorLeft P ⋙ Bimod.forget R

/-- The underlying-object functor of balanced tensor product with a fixed right bimodule. -/
@[stacks 0FSA "underlying generic balanced tensor functor in the left bimodule"]
def tensorRightUnderlying (Q : Bimod S T) : Bimod R S ⥤ C :=
  tensorRight Q ⋙ Bimod.forget R

/-- Evaluating `tensorLeft` gives Mathlib's coequalizer-based balanced tensor product. -/
@[simp]
theorem tensorLeft_obj (P : Bimod R S) (Q : Bimod S T) :
    (tensorLeft P).obj Q = P.tensorBimod Q := sorry

/-- The map of `tensorLeft` is left whiskering of a bimodule morphism. -/
@[simp]
theorem tensorLeft_map {Q Q' : Bimod S T} (P : Bimod R S) (f : Q ⟶ Q') :
    (tensorLeft P).map f = Bimod.whiskerLeft P f := sorry

/-- Evaluating `tensorRight` gives Mathlib's coequalizer-based balanced tensor product. -/
@[simp]
theorem tensorRight_obj (P : Bimod R S) (Q : Bimod S T) :
    (tensorRight Q).obj P = P.tensorBimod Q := sorry

/-- The map of `tensorRight` is right whiskering of a bimodule morphism. -/
@[simp]
theorem tensorRight_map {P P' : Bimod R S} (f : P ⟶ P') (Q : Bimod S T) :
    (tensorRight Q).map f = Bimod.whiskerRight f Q := sorry

/-- The underlying object of the left-variable balanced tensor functor is the canonical
coequalizer defining the relative tensor product. -/
@[simp]
theorem tensorLeftUnderlying_obj (P : Bimod R S) (Q : Bimod S T) :
    (tensorLeftUnderlying P).obj Q = (P.tensorBimod Q).X := sorry

/-- The underlying object of the right-variable balanced tensor functor is the canonical
coequalizer defining the relative tensor product. -/
@[simp]
theorem tensorRightUnderlying_obj (P : Bimod R S) (Q : Bimod S T) :
    (tensorRightUnderlying Q).obj P = (P.tensorBimod Q).X := sorry

end CategoryTheory.Bimod

end
