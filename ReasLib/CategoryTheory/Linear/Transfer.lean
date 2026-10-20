/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Preadditive.Transfer
public import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pulling back linear structures along fully faithful functors

There are two complementary interfaces. If the source already has a preadditive structure and
the fully faithful functor is additive, only the linear structure is pulled back. If the source
has no chosen preadditive structure, the bootstrap interface pulls back both structures together.
The two cases have distinct names so that downstream code cannot silently switch structures.
-/

@[expose] public section

noncomputable section

namespace CategoryTheory

universe w v₁ v₂ u₁ u₂

variable {R : Type w} [Semiring R]
variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D] [Preadditive D]
variable [linearD : CategoryTheory.Linear R D]
variable {F : C ⥤ D}

namespace Linear

/-- Pull back an `R`-linear structure together with the preadditive structure induced by a fully
faithful functor. -/
@[stacks 09MJ "linear structure and preadditive structure induced by a fully faithful functor",
  implicit_reducible]
noncomputable def ofFullyFaithfulInduced (hF : F.FullyFaithful) :
    @Linear R _ C _ (Preadditive.ofFullyFaithful hF) :=
  @Linear.mk R _ C _ (Preadditive.ofFullyFaithful hF)
    (fun X Y ↦ @Equiv.module R (X ⟶ Y) (F.obj X ⟶ F.obj Y) _ hF.homEquiv
      (@Preadditive.homGroup D _ _ (F.obj X) (F.obj Y)).toAddCommMonoid
      (@Linear.homModule R _ D _ _ linearD (F.obj X) (F.obj Y)))
    sorry sorry

end Linear

namespace Functor.FullyFaithful

/-- The Hom equivalence is linear for the preadditive and linear structures induced by the same
fully faithful functor. -/
@[stacks 09MJ "linear Hom equivalence for the induced source structures"]
noncomputable def homLinearEquivInduced (hF : F.FullyFaithful) {X Y : C} :
    @LinearEquiv R R _ _ (RingHom.id R) _ _ _ (X ⟶ Y) (F.obj X ⟶ F.obj Y)
      (@Preadditive.homGroup C _ (Preadditive.ofFullyFaithful hF) X Y).toAddCommMonoid
      (@Preadditive.homGroup D _ _ (F.obj X) (F.obj Y)).toAddCommMonoid
      (@CategoryTheory.Linear.homModule R _ C _ (Preadditive.ofFullyFaithful hF)
        (CategoryTheory.Linear.ofFullyFaithfulInduced hF) X Y)
      (@CategoryTheory.Linear.homModule R _ D _ _ linearD (F.obj X) (F.obj Y)) :=
  @Equiv.linearEquiv R (X ⟶ Y) (F.obj X ⟶ F.obj Y) _ hF.homEquiv
    (@Preadditive.homGroup D _ _ (F.obj X) (F.obj Y)).toAddCommMonoid
    (@CategoryTheory.Linear.homModule R _ D _ _ linearD (F.obj X) (F.obj Y))

/-- The induced Hom linear equivalence acts by the functor map. -/
@[simp]
theorem homLinearEquivInduced_apply (hF : F.FullyFaithful) {X Y : C} (f : X ⟶ Y) :
    hF.homLinearEquivInduced (R := R) f = F.map f := sorry

/-- A fully faithful functor is linear for the preadditive and linear structures induced by
itself. -/
theorem linear_ofFullyFaithfulInduced (hF : F.FullyFaithful) :
    @Functor.Linear R _ C D _ _ (Preadditive.ofFullyFaithful hF) _
      (CategoryTheory.Linear.ofFullyFaithfulInduced hF) linearD F := sorry

end Functor.FullyFaithful

section ExistingPreadditive

variable [Preadditive C]

namespace Functor.FullyFaithful

/-- The Hom equivalence of a fully faithful additive functor is additive for the existing
preadditive structures. -/
@[stacks 09MJ "additive Hom equivalence of a fully faithful additive functor"]
noncomputable def homAddEquiv (hF : F.FullyFaithful) [F.Additive] {X Y : C} :
    (X ⟶ Y) ≃+ (F.obj X ⟶ F.obj Y) where
  toEquiv := hF.homEquiv
  map_add' := sorry

/-- The additive Hom equivalence acts by the functor map. -/
@[simp]
theorem homAddEquiv_apply (hF : F.FullyFaithful) [F.Additive]
    {X Y : C} (f : X ⟶ Y) :
    hF.homAddEquiv f = F.map f := sorry

end Functor.FullyFaithful

namespace Linear

/-- Pull back an `R`-linear structure along a fully faithful additive functor while preserving
the existing preadditive structure on the source. -/
@[stacks 09MJ "linear structure induced by a fully faithful additive functor",
  implicit_reducible]
noncomputable def ofFullyFaithful (hF : F.FullyFaithful) [F.Additive] :
    Linear R C where
  homModule X Y :=
    @AddEquiv.module (X ⟶ Y) (F.obj X ⟶ F.obj Y) R _
      (@Preadditive.homGroup C _ _ X Y).toAddCommMonoid
      (@Preadditive.homGroup D _ _ (F.obj X) (F.obj Y)).toAddCommMonoid
      (@CategoryTheory.Linear.homModule R _ D _ _ linearD (F.obj X) (F.obj Y))
      (hF.homAddEquiv (X := X) (Y := Y))
  smul_comp := sorry
  comp_smul := sorry

end Linear

namespace Functor.FullyFaithful

/-- A fully faithful additive functor is linear for the linear structure pulled back along it. -/
theorem linear_ofFullyFaithful (hF : F.FullyFaithful) [F.Additive] :
    @Functor.Linear R _ C D _ _ _ _
      (CategoryTheory.Linear.ofFullyFaithful hF) linearD F := sorry

/-- A fully faithful additive linear functor induces a linear equivalence on Hom modules. -/
@[stacks 09MJ "linear Hom equivalence of a fully faithful linear functor"]
noncomputable def homLinearEquiv (hF : F.FullyFaithful)
    [linearC : CategoryTheory.Linear R C] [F.Additive] [F.Linear R] {X Y : C} :
    (X ⟶ Y) ≃ₗ[R] (F.obj X ⟶ F.obj Y) where
  toAddEquiv := hF.homAddEquiv
  map_smul' := sorry

/-- The linear Hom equivalence acts by the functor map. -/
@[simp]
theorem homLinearEquiv_apply (hF : F.FullyFaithful)
    [linearC : CategoryTheory.Linear R C] [F.Additive] [F.Linear R]
    {X Y : C} (f : X ⟶ Y) :
    hF.homLinearEquiv (R := R) f = F.map f := sorry

end Functor.FullyFaithful

end ExistingPreadditive

end CategoryTheory

end
