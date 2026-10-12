/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Functor.Derived.ComputesAt.Value.Explicit
public import ReasLib.CategoryTheory.Functor.Derived.PointwiseValue.Inverted

/-!
# Pointwise Derived Values Computed by Replacements

A denominator whose appropriate endpoint computes a derived value gives an isomorphism directly
to or from the pointwise derived value.  These comparisons require neither a total derived
functor nor a chosen localization model beyond the canonical pointwise construction.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  (F : D ⥤ D') (S : MorphismProperty D) [S.ContainsIdentities]

namespace RightDerived.Value

/-- A right-derived denominator leg is invertible when its target computes the pointwise
right-derived value. -/
@[stacks 05SX "pointwise right-derived value computed by a replacement"]
theorem isIso_ι_of_computesAt {X Y : D} (s : X ⟶ Y) (hs : S s)
    [F.HasPointwiseRightDerivedFunctorAt S X]
    (hY : RightDerived.ComputesAt F S Y) : IsIso (ι F S s hs) := sorry

/-- A replacement by a computing object identifies its original value with the pointwise
right-derived value of the source. -/
@[stacks 05SX "pointwise right-derived replacement comparison"]
noncomputable def replacementIso {X Y : D} (s : X ⟶ Y) (hs : S s)
    [F.HasPointwiseRightDerivedFunctorAt S X]
    (hY : RightDerived.ComputesAt F S Y) :
    F.obj Y ≅ obj F S X :=
  @asIso _ _ _ _ (ι F S s hs) (isIso_ι_of_computesAt F S s hs hY)

/-- The forward pointwise replacement comparison is the canonical denominator leg. -/
@[simp, stacks 05SX "pointwise right-derived replacement comparison, hom"]
theorem replacementIso_hom {X Y : D} (s : X ⟶ Y) (hs : S s)
    [F.HasPointwiseRightDerivedFunctorAt S X]
    (hY : RightDerived.ComputesAt F S Y) :
    (replacementIso F S s hs hY).hom = ι F S s hs := sorry

/-- The inverse pointwise replacement comparison is the inverse denominator leg. -/
@[simp, stacks 05SX "pointwise right-derived replacement comparison, inv"]
theorem replacementIso_inv {X Y : D} (s : X ⟶ Y) (hs : S s)
    [F.HasPointwiseRightDerivedFunctorAt S X]
    (hY : RightDerived.ComputesAt F S Y) :
    (replacementIso F S s hs hY).inv =
      @CategoryTheory.inv _ _ _ _ (ι F S s hs)
        (isIso_ι_of_computesAt F S s hs hY) := sorry

/-- Pointwise right-derived replacement comparisons are natural in commutative squares of
denominators. -/
@[reassoc, stacks 05SX "naturality of pointwise right-derived replacements"]
theorem replacementIso_hom_naturality
    {X₁ X₂ Y₁ Y₂ : D}
    [F.HasPointwiseRightDerivedFunctorAt S X₁]
    [F.HasPointwiseRightDerivedFunctorAt S Y₁]
    (sX : X₁ ⟶ X₂) (hsX : S sX) (hX₂ : RightDerived.ComputesAt F S X₂)
    (sY : Y₁ ⟶ Y₂) (hsY : S sY) (hY₂ : RightDerived.ComputesAt F S Y₂)
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) (comm : sX ≫ g = f ≫ sY) :
    F.map g ≫ (replacementIso F S sY hsY hY₂).hom =
      (replacementIso F S sX hsX hX₂).hom ≫ map F S f := sorry

/-- The inverses of pointwise right-derived replacement comparisons satisfy reverse
naturality. -/
@[reassoc, stacks 05SX "inverse naturality of pointwise right-derived replacements"]
theorem replacementIso_inv_naturality
    {X₁ X₂ Y₁ Y₂ : D}
    [F.HasPointwiseRightDerivedFunctorAt S X₁]
    [F.HasPointwiseRightDerivedFunctorAt S Y₁]
    (sX : X₁ ⟶ X₂) (hsX : S sX) (hX₂ : RightDerived.ComputesAt F S X₂)
    (sY : Y₁ ⟶ Y₂) (hsY : S sY) (hY₂ : RightDerived.ComputesAt F S Y₂)
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) (comm : sX ≫ g = f ≫ sY) :
    (replacementIso F S sX hsX hX₂).inv ≫ F.map g =
      map F S f ≫ (replacementIso F S sY hsY hY₂).inv := sorry

end RightDerived.Value

namespace LeftDerived.Value

/-- A left-derived denominator projection is invertible when its source computes the pointwise
left-derived value. -/
@[stacks 05SX "pointwise left-derived value computed by a coreplacement"]
theorem isIso_π_of_computesAt {X Y : D} (s : X ⟶ Y) (hs : S s)
    [F.HasPointwiseLeftDerivedFunctorAt S Y]
    (hX : LeftDerived.ComputesAt F S X) : IsIso (π F S s hs) := sorry

/-- A coreplacement by a computing object identifies the pointwise left-derived value of the
target with the original value at the source. -/
@[stacks 05SX "pointwise left-derived coreplacement comparison"]
noncomputable def coreplacementIso {X Y : D} (s : X ⟶ Y) (hs : S s)
    [F.HasPointwiseLeftDerivedFunctorAt S Y]
    (hX : LeftDerived.ComputesAt F S X) :
    obj F S Y ≅ F.obj X :=
  @asIso _ _ _ _ (π F S s hs) (isIso_π_of_computesAt F S s hs hX)

/-- The forward pointwise coreplacement comparison is the canonical denominator projection. -/
@[simp, stacks 05SX "pointwise left-derived coreplacement comparison, hom"]
theorem coreplacementIso_hom {X Y : D} (s : X ⟶ Y) (hs : S s)
    [F.HasPointwiseLeftDerivedFunctorAt S Y]
    (hX : LeftDerived.ComputesAt F S X) :
    (coreplacementIso F S s hs hX).hom = π F S s hs := sorry

/-- The inverse pointwise coreplacement comparison is the inverse denominator projection. -/
@[simp, stacks 05SX "pointwise left-derived coreplacement comparison, inv"]
theorem coreplacementIso_inv {X Y : D} (s : X ⟶ Y) (hs : S s)
    [F.HasPointwiseLeftDerivedFunctorAt S Y]
    (hX : LeftDerived.ComputesAt F S X) :
    (coreplacementIso F S s hs hX).inv =
      @CategoryTheory.inv _ _ _ _ (π F S s hs)
        (isIso_π_of_computesAt F S s hs hX) := sorry

/-- Pointwise left-derived coreplacement comparisons are natural in commutative squares of
denominators. -/
@[reassoc, stacks 05SX "naturality of pointwise left-derived coreplacements"]
theorem coreplacementIso_hom_naturality
    {X₁ X₂ Y₁ Y₂ : D}
    [F.HasPointwiseLeftDerivedFunctorAt S X₂]
    [F.HasPointwiseLeftDerivedFunctorAt S Y₂]
    (sX : X₁ ⟶ X₂) (hsX : S sX) (hX₁ : LeftDerived.ComputesAt F S X₁)
    (sY : Y₁ ⟶ Y₂) (hsY : S sY) (hY₁ : LeftDerived.ComputesAt F S Y₁)
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) (comm : sX ≫ g = f ≫ sY) :
    map F S g ≫ (coreplacementIso F S sY hsY hY₁).hom =
      (coreplacementIso F S sX hsX hX₁).hom ≫ F.map f := sorry

/-- The inverses of pointwise left-derived coreplacement comparisons satisfy reverse
naturality. -/
@[reassoc, stacks 05SX "inverse naturality of pointwise left-derived coreplacements"]
theorem coreplacementIso_inv_naturality
    {X₁ X₂ Y₁ Y₂ : D}
    [F.HasPointwiseLeftDerivedFunctorAt S X₂]
    [F.HasPointwiseLeftDerivedFunctorAt S Y₂]
    (sX : X₁ ⟶ X₂) (hsX : S sX) (hX₁ : LeftDerived.ComputesAt F S X₁)
    (sY : Y₁ ⟶ Y₂) (hsY : S sY) (hY₁ : LeftDerived.ComputesAt F S Y₁)
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) (comm : sX ≫ g = f ≫ sY) :
    (coreplacementIso F S sX hsX hX₁).inv ≫ map F S g =
      F.map f ≫ (coreplacementIso F S sY hsY hY₁).inv := sorry

end LeftDerived.Value

end CategoryTheory.Functor
