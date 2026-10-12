/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Functor.Derived.ComputesAt
public import ReasLib.CategoryTheory.Functor.Derived.PointwiseValue.IdentityDenominator

@[expose] public section

/-!
# Values at Objects Computing a Derived Functor

The identity-denominator leg or projection identifies the original value with the pointwise
derived value at every computing object.  This local API requires neither global definedness nor
a chosen model of the derived functor.
-/

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  (F : D ⥤ D') (S : MorphismProperty D) [S.ContainsIdentities]

/-- At an object computing the right-derived functor, the identity-denominator leg identifies
the original value with the pointwise right-derived value. -/
@[stacks 05SX "right-derived value at a computing object"]
noncomputable def RightDerived.ComputesAt.valueIso (X : D)
    [RightDerived.ComputesAt F S X] :
    F.obj X ≅ RightDerived.Value.obj F S X :=
  asIso (RightDerived.Value.ι F S (𝟙 X) (S.id_mem X))

/-- The forward map of the right-derived computation isomorphism is the identity-denominator
leg. -/
@[simp, stacks 05SX "right-derived computing isomorphism, hom"]
theorem RightDerived.ComputesAt.valueIso_hom (X : D)
    [RightDerived.ComputesAt F S X] :
    (RightDerived.ComputesAt.valueIso F S X).hom =
      RightDerived.Value.ι F S (𝟙 X) (S.id_mem X) := sorry

/-- The inverse map of the right-derived computation isomorphism is the inverse
identity-denominator leg. -/
@[simp, stacks 05SX "right-derived computing isomorphism, inv"]
theorem RightDerived.ComputesAt.valueIso_inv (X : D)
    [RightDerived.ComputesAt F S X] :
    (RightDerived.ComputesAt.valueIso F S X).inv =
      @CategoryTheory.inv _ _ _ _
        (RightDerived.Value.ι F S (𝟙 X) (S.id_mem X)) inferInstance := sorry

/-- The forward right-derived computation isomorphisms are natural between computing
objects. -/
@[reassoc, stacks 05SX "naturality of right-derived computing isomorphisms"]
theorem RightDerived.ComputesAt.valueIso_hom_naturality
    {X Y : D} (f : X ⟶ Y)
    [RightDerived.ComputesAt F S X] [RightDerived.ComputesAt F S Y] :
    (RightDerived.ComputesAt.valueIso F S X).hom ≫ RightDerived.Value.map F S f =
      F.map f ≫ (RightDerived.ComputesAt.valueIso F S Y).hom := sorry

/-- The inverse right-derived computation isomorphisms satisfy the reverse naturality
equation. -/
@[reassoc, stacks 05SX "inverse naturality of right-derived computing isomorphisms"]
theorem RightDerived.ComputesAt.valueIso_inv_naturality
    {X Y : D} (f : X ⟶ Y)
    [RightDerived.ComputesAt F S X] [RightDerived.ComputesAt F S Y] :
    RightDerived.Value.map F S f ≫ (RightDerived.ComputesAt.valueIso F S Y).inv =
      (RightDerived.ComputesAt.valueIso F S X).inv ≫ F.map f := sorry

/-- At an object computing the left-derived functor, the identity-denominator projection
identifies the pointwise left-derived value with the original value. -/
@[stacks 05SX "left-derived value at a computing object"]
noncomputable def LeftDerived.ComputesAt.valueIso (X : D)
    [LeftDerived.ComputesAt F S X] :
    LeftDerived.Value.obj F S X ≅ F.obj X :=
  asIso (LeftDerived.Value.π F S (𝟙 X) (S.id_mem X))

/-- The forward map of the left-derived computation isomorphism is the identity-denominator
projection. -/
@[simp, stacks 05SX "left-derived computing isomorphism, hom"]
theorem LeftDerived.ComputesAt.valueIso_hom (X : D)
    [LeftDerived.ComputesAt F S X] :
    (LeftDerived.ComputesAt.valueIso F S X).hom =
      LeftDerived.Value.π F S (𝟙 X) (S.id_mem X) := sorry

/-- The inverse map of the left-derived computation isomorphism is the inverse
identity-denominator projection. -/
@[simp, stacks 05SX "left-derived computing isomorphism, inv"]
theorem LeftDerived.ComputesAt.valueIso_inv (X : D)
    [LeftDerived.ComputesAt F S X] :
    (LeftDerived.ComputesAt.valueIso F S X).inv =
      @CategoryTheory.inv _ _ _ _
        (LeftDerived.Value.π F S (𝟙 X) (S.id_mem X)) inferInstance := sorry

/-- The forward left-derived computation isomorphisms are natural between computing
objects. -/
@[reassoc, stacks 05SX "naturality of left-derived computing isomorphisms"]
theorem LeftDerived.ComputesAt.valueIso_hom_naturality
    {X Y : D} (f : X ⟶ Y)
    [LeftDerived.ComputesAt F S X] [LeftDerived.ComputesAt F S Y] :
    LeftDerived.Value.map F S f ≫ (LeftDerived.ComputesAt.valueIso F S Y).hom =
      (LeftDerived.ComputesAt.valueIso F S X).hom ≫ F.map f := sorry

/-- The inverse left-derived computation isomorphisms satisfy the reverse naturality
equation. -/
@[reassoc, stacks 05SX "inverse naturality of left-derived computing isomorphisms"]
theorem LeftDerived.ComputesAt.valueIso_inv_naturality
    {X Y : D} (f : X ⟶ Y)
    [LeftDerived.ComputesAt F S X] [LeftDerived.ComputesAt F S Y] :
    F.map f ≫ (LeftDerived.ComputesAt.valueIso F S Y).inv =
      (LeftDerived.ComputesAt.valueIso F S X).inv ≫ LeftDerived.Value.map F S f := sorry



end CategoryTheory.Functor
