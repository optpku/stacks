module

public import ReasLib.CategoryTheory.Functor.Derived.PointwiseValue.Left
public import ReasLib.CategoryTheory.Functor.Derived.PointwiseValue.Right

/-!
# Denominators Act Invertibly on Pointwise Derived Values

The map between two pointwise derived values induced by a denominator is invertible whenever
both endpoint values exist.  This local statement does not require a globally defined or total
derived functor.
-/

@[expose] public section

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  (F : D ⥤ D') (S : MorphismProperty D)

namespace RightDerived.Value

/-- A denominator induces an isomorphism between its two pointwise right-derived values. -/
@[stacks 05SA "denominator inversion on pointwise right-derived values"]
theorem map_isIso_of_mem {X Y : D} (f : X ⟶ Y) (hf : S f)
    [F.HasPointwiseRightDerivedFunctorAt S X]
    [F.HasPointwiseRightDerivedFunctorAt S Y] :
    IsIso (map F S f) := sorry

/-- The isomorphism between pointwise right-derived values induced by a denominator. -/
@[stacks 05SA "denominator isomorphism on pointwise right-derived values"]
noncomputable def mapIsoOfMem {X Y : D} (f : X ⟶ Y) (hf : S f)
    [F.HasPointwiseRightDerivedFunctorAt S X]
    [F.HasPointwiseRightDerivedFunctorAt S Y] :
    obj F S X ≅ obj F S Y :=
  @asIso _ _ _ _ (map F S f) (map_isIso_of_mem F S f hf)

/-- The forward map of a pointwise right-derived denominator isomorphism is the canonical
pointwise map. -/
@[simp, stacks 05SA "denominator isomorphism on pointwise right-derived values, hom"]
theorem mapIsoOfMem_hom {X Y : D} (f : X ⟶ Y) (hf : S f)
    [F.HasPointwiseRightDerivedFunctorAt S X]
    [F.HasPointwiseRightDerivedFunctorAt S Y] :
    (mapIsoOfMem F S f hf).hom = map F S f := sorry

/-- The inverse map of a pointwise right-derived denominator isomorphism is the inverse of the
canonical pointwise map. -/
@[simp, stacks 05SA "denominator isomorphism on pointwise right-derived values, inv"]
theorem mapIsoOfMem_inv {X Y : D} (f : X ⟶ Y) (hf : S f)
    [F.HasPointwiseRightDerivedFunctorAt S X]
    [F.HasPointwiseRightDerivedFunctorAt S Y] :
    (mapIsoOfMem F S f hf).inv =
      @CategoryTheory.inv _ _ _ _ (map F S f) (map_isIso_of_mem F S f hf) := sorry

end RightDerived.Value

namespace LeftDerived.Value

/-- A denominator induces an isomorphism between its two pointwise left-derived values. -/
@[stacks 05SA "denominator inversion on pointwise left-derived values"]
theorem map_isIso_of_mem {X Y : D} (f : X ⟶ Y) (hf : S f)
    [F.HasPointwiseLeftDerivedFunctorAt S X]
    [F.HasPointwiseLeftDerivedFunctorAt S Y] :
    IsIso (map F S f) := sorry

/-- The isomorphism between pointwise left-derived values induced by a denominator. -/
@[stacks 05SA "denominator isomorphism on pointwise left-derived values"]
noncomputable def mapIsoOfMem {X Y : D} (f : X ⟶ Y) (hf : S f)
    [F.HasPointwiseLeftDerivedFunctorAt S X]
    [F.HasPointwiseLeftDerivedFunctorAt S Y] :
    obj F S X ≅ obj F S Y :=
  @asIso _ _ _ _ (map F S f) (map_isIso_of_mem F S f hf)

/-- The forward map of a pointwise left-derived denominator isomorphism is the canonical
pointwise map. -/
@[simp, stacks 05SA "denominator isomorphism on pointwise left-derived values, hom"]
theorem mapIsoOfMem_hom {X Y : D} (f : X ⟶ Y) (hf : S f)
    [F.HasPointwiseLeftDerivedFunctorAt S X]
    [F.HasPointwiseLeftDerivedFunctorAt S Y] :
    (mapIsoOfMem F S f hf).hom = map F S f := sorry

/-- The inverse map of a pointwise left-derived denominator isomorphism is the inverse of the
canonical pointwise map. -/
@[simp, stacks 05SA "denominator isomorphism on pointwise left-derived values, inv"]
theorem mapIsoOfMem_inv {X Y : D} (f : X ⟶ Y) (hf : S f)
    [F.HasPointwiseLeftDerivedFunctorAt S X]
    [F.HasPointwiseLeftDerivedFunctorAt S Y] :
    (mapIsoOfMem F S f hf).inv =
      @CategoryTheory.inv _ _ _ _ (map F S f) (map_isIso_of_mem F S f hf) := sorry

end LeftDerived.Value

end CategoryTheory.Functor
