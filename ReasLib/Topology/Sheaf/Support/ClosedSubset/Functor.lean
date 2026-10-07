module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import ReasLib.Topology.Sheaf.Support.ClosedSubset.Kernel

/-!
# Functorial sections with support in a closed subset

This module specializes the coefficient-generic ambient kernel functor to additive sheaves and
then restricts it to the closed subspace.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace

noncomputable section

universe w u

namespace TopCat.Sheaf.ClosedSubset.SectionsWithSupport

section Generic

variable {X : TopCat.{w}} {Z : Set X}
variable {C : Type u} [Category.{w} C]
variable {FC : C → C → Type w} {CC : C → Type w}
variable [∀ A B, FunLike (FC A B) (CC A) (CC B)] [ConcreteCategory.{w} C FC]
variable [IsAlgebraicStructure C (CategoryTheory.forget C)]
variable [HasColimits C] [HasZeroMorphisms C]

/-- Remark 17.6.2 (01AY): the coefficient-generic sheaf on the closed subspace obtained by
restricting the ambient kernel of restriction to the open complement. -/
@[stacks 01AY "closed-subspace sheaf"]
def sheaf (hZ : IsClosed Z) (F : X.Sheaf C) :
    (TopCat.of Z).Sheaf C :=
  (Sheaf.pullback C (TopCat.subsetInclusion Z)).obj (object hZ F)

/-- Naturality of restriction to the open complement with respect to a morphism of sheaves. -/
theorem subsheafMap_w
    (hZ : IsClosed Z) {F G : X.Sheaf C} (f : F ⟶ G) :
    f ≫ restrictionToComplement hZ G =
      restrictionToComplement hZ F ≫
        (Sheaf.pushforward C (openComplementInclusion hZ)).map
          ((Sheaf.pullback C (openComplementInclusion hZ)).map f) := sorry

/-- The morphism between ambient closed-support objects induced by a morphism of sheaves. -/
abbrev subsheafMap
    (hZ : IsClosed Z) {F G : X.Sheaf C} (f : F ⟶ G) :
    object hZ F ⟶ object hZ G :=
  (ambientFunctor (C := C) hZ).map f

/-- The map on closed-support objects commutes with their canonical inclusions. -/
theorem subsheafMap_comp_inclusion
    (hZ : IsClosed Z) {F G : X.Sheaf C} (f : F ⟶ G) :
    subsheafMap hZ f ≫ inclusion hZ G = inclusion hZ F ≫ f := sorry

/-- Remark 17.6.2 (01AY) (3): the coefficient-generic functor sending a sheaf on `X` to its sheaf
of sections vanishing on the complement of the closed subset `Z`. -/
@[stacks 01AY "(3)"]
noncomputable def functor (hZ : IsClosed Z) :
    CategoryTheory.Functor (X.Sheaf C) ((TopCat.of Z).Sheaf C) :=
  ambientFunctor (C := C) hZ ⋙ Sheaf.pullback C (TopCat.subsetInclusion Z)

/-- Evaluation of the closed-support functor is restriction of its ambient kernel object. -/
@[simp]
theorem functor_obj
    (hZ : IsClosed Z) (F : X.Sheaf C) :
    (functor hZ).obj F = sheaf hZ F := sorry

/-- The morphism part of the closed-support functor is induced by the ambient kernel functor. -/
@[simp]
theorem functor_map
    (hZ : IsClosed Z) {F G : X.Sheaf C} (f : F ⟶ G) :
    (functor hZ).map f =
      (Sheaf.pullback C (TopCat.subsetInclusion Z)).map (subsheafMap hZ f) := sorry

end Generic

section AddCommGrp

variable {X : TopCat.{u}} {Z : Set X}
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]

/-- Remark 17.6.2 (01AY): preservation of finite limits by the closed-support functor is
available to typeclass search. -/
@[stacks 01AY "left-exact instance"]
noncomputable instance functorPreservesFiniteLimits (hZ : IsClosed Z) :
    PreservesFiniteLimits (functor (C := AddCommGrpCat.{u}) hZ) := sorry

/-- Remark 17.6.2 (01AY) (4): the functor of sections supported on a closed subset is left
exact. -/
@[stacks 01AY "(4)"]
theorem functorLeftExact (hZ : IsClosed Z) :
    leftExactFunctor (X.Sheaf AddCommGrpCat.{u})
      ((TopCat.of Z).Sheaf AddCommGrpCat.{u})
        (functor (C := AddCommGrpCat.{u}) hZ) := sorry

end AddCommGrp

end TopCat.Sheaf.ClosedSubset.SectionsWithSupport

end
