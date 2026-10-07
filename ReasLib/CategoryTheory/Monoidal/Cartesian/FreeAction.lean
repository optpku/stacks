module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod

@[expose] public section

open CategoryTheory

universe v u

namespace CategoryTheory.ModObj

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

/-- The shear morphism of a group object action is a monomorphism if and only if
the induced action on every type of generalized points is free. -/
theorem mono_leftSMul_iff (M X : C) [GrpObj M] [ModObj M X] :
    Mono (leftSMul M X) ↔ ∀ Z : C, IsCancelSMul (Z ⟶ M) (Z ⟶ X) := sorry

/-- Monicity of the shear morphism gives freeness on generalized points. -/
instance instIsCancelSMulOfMonoLeftSMul (M X Z : C) [GrpObj M] [ModObj M X]
    [Mono (leftSMul M X)] : IsCancelSMul (Z ⟶ M) (Z ⟶ X) := sorry

end CategoryTheory.ModObj

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  {G : C} [GrpObj G]

/-- A module object is free when the induced action on every type of generalized points is free. -/
class IsFree (X : Mod C G) : Prop where
  /-- For every object `Z`, the induced action of `(Z ⟶ G)` on `(Z ⟶ X.X)` is cancellative. -/
  isCancelSMul (Z : C) : IsCancelSMul (Z ⟶ G) (Z ⟶ X.X)

namespace IsFree

/-- A free action is free on every generalized-point object. -/
instance instIsCancelSMul (X : Mod C G) (Z : C) [IsFree X] :
    IsCancelSMul (Z ⟶ G) (Z ⟶ X.X) :=
  IsFree.isCancelSMul (X := X) Z

end IsFree

/-- Freeness means cancellation on every type of generalized points. -/
theorem isFree_iff (X : Mod C G) :
    IsFree X ↔ ∀ Z : C, IsCancelSMul (Z ⟶ G) (Z ⟶ X.X) := by
  constructor
  · intro hX Z
    exact hX.isCancelSMul Z
  · intro hX
    exact ⟨hX⟩

/-- Freeness is equivalent to monicity of the shear morphism. -/
theorem isFree_iff_mono_leftSMul (X : Mod C G) :
    IsFree X ↔ Mono (ModObj.leftSMul G X.X) :=
  (isFree_iff X).trans (ModObj.mono_leftSMul_iff G X.X).symm

/-- A free action has monic shear morphism. -/
instance instMonoLeftSMul (X : Mod C G) [IsFree X] :
    Mono (ModObj.leftSMul G X.X) :=
  (isFree_iff_mono_leftSMul X).mp inferInstance

end CategoryTheory.Mod
