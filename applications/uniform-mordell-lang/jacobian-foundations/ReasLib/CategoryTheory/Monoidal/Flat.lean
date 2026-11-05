module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import ReasLib.CategoryTheory.Monoidal.Invertible
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Flat objects in a monoidal category

Flatness is owned at the monoidal-category level: an object is flat when tensoring on the
right by it is exact.  Module presheaves and module sheaves expose thin specializations of this
owner rather than defining parallel notions.
-/

@[expose] public section

open CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- An object of a monoidal category is flat when tensoring on the right by it is exact. -/
@[stacks 03ER "categorical owner"]
class IsFlat (X : C) : Prop where
  /-- Tensoring on the right by a flat object is exact. -/
  exact_tensor : exactFunctor C C (tensorRight X)

/-- The object property of being flat in a monoidal category. -/
abbrev flatObjects : ObjectProperty C :=
  fun X ↦ IsFlat X

/-- Flat objects are closed under isomorphisms. -/
instance flatObjects_isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms (flatObjects (C := C)) where
  of_iso e hX :=
    ⟨ObjectProperty.prop_of_iso (exactFunctor C C)
      ((tensoringRight C).mapIso e) hX.exact_tensor⟩

/-- Flatness transports along an isomorphism. -/
theorem IsFlat.ofIso {X Y : C} (hX : IsFlat X) (e : X ≅ Y) : IsFlat Y :=
  ObjectProperty.prop_of_iso flatObjects e hX

/-- A flat presentation of `X` consists of an epimorphism from a flat object. -/
structure FlatPresentation (X : C) where
  /-- The flat source of the presentation. -/
  source : C
  /-- The source is flat. -/
  isFlat : IsFlat source
  /-- The presentation morphism. -/
  map : source ⟶ X
  /-- The presentation morphism is an epimorphism. -/
  epi_map : Epi map

namespace FlatPresentation

/-- Package a specified epimorphism from a specified flat object as a flat presentation. -/
def ofEpi {X P : C} [IsFlat P] (p : P ⟶ X) [Epi p] : FlatPresentation X where
  source := P
  isFlat := inferInstance
  map := p
  epi_map := inferInstance

end FlatPresentation

/-- A monoidal category has enough flat objects if every object admits a flat presentation. -/
class EnoughFlatObjects (C : Type u) [Category.{v} C] [MonoidalCategory C] : Prop where
  /-- A flat presentation exists for every object. -/
  presentation : ∀ X : C, Nonempty (FlatPresentation X)

/-- Tensoring on the right by a flat object is exact. -/
theorem IsFlat.exactTensor (X : C) [IsFlat X] :
    exactFunctor C C (tensorRight X) :=
  IsFlat.exact_tensor

/-- Tensoring on the right by a flat object, bundled as an exact functor. -/
noncomputable abbrev IsFlat.exactTensorRight (X : C) [IsFlat X] : C ⥤ₑ C :=
  ⟨tensorRight X, exactTensor X⟩

/-- In a braided monoidal category, tensoring on the left by a flat object is exact. -/
theorem IsFlat.exact_tensorLeft [BraidedCategory C] (X : C) [IsFlat X] :
    exactFunctor C C (tensorLeft X) :=
  ObjectProperty.prop_of_iso (exactFunctor C C)
    (BraidedCategory.tensorLeftIsoTensorRight X).symm IsFlat.exact_tensor

/-- In a braided monoidal category, tensoring on the left by a flat object, bundled as an exact
functor. -/
noncomputable abbrev IsFlat.exactTensorLeft [BraidedCategory C] (X : C) [IsFlat X] : C ⥤ₑ C :=
  ⟨tensorLeft X, exact_tensorLeft X⟩

/-- Right tensoring by a flat object preserves finite limits.  This is the typeclass-facing
projection of `IsFlat.exactTensor`. -/
@[stacks 03ER "right tensor preserves finite limits", instance]
theorem IsFlat.tensorRightPreservesFiniteLimits (X : C) [IsFlat X] :
    PreservesFiniteLimits (tensorRight X) :=
  (IsFlat.exactTensor X).1

/-- Right tensoring by a flat object preserves finite colimits.  This is the typeclass-facing
projection of `IsFlat.exactTensor`. -/
@[stacks 03ER "right tensor preserves finite colimits", instance]
theorem IsFlat.tensorRightPreservesFiniteColimits (X : C) [IsFlat X] :
    PreservesFiniteColimits (tensorRight X) :=
  (IsFlat.exactTensor X).2

/-- In a braided monoidal category, left tensoring by a flat object preserves finite limits. -/
@[stacks 03ER "left tensor preserves finite limits", instance]
theorem IsFlat.tensorLeftPreservesFiniteLimits [BraidedCategory C]
    (X : C) [IsFlat X] : PreservesFiniteLimits (tensorLeft X) :=
  (IsFlat.exact_tensorLeft X).1

/-- In a braided monoidal category, left tensoring by a flat object preserves finite colimits. -/
@[stacks 03ER "left tensor preserves finite colimits", instance]
theorem IsFlat.tensorLeftPreservesFiniteColimits [BraidedCategory C]
    (X : C) [IsFlat X] : PreservesFiniteColimits (tensorLeft X) :=
  (IsFlat.exact_tensorLeft X).2

/-- Flatness is exactly exactness of the right-tensor functor. -/
theorem isFlat_iff (X : C) :
    IsFlat X ↔ exactFunctor C C (tensorRight X) := by
  constructor
  · exact fun h ↦ h.exact_tensor
  · exact fun h ↦ ⟨h⟩

/-- Every tensor-invertible object is flat: the associated tensor equivalence is exact. -/
@[stacks 0B8N "consequence (1), flat"]
instance isFlat_of_isInvertibleObject (X : C) [isInvertibleObject X] : IsFlat X := by
  constructor
  rw [exactFunctor_iff]
  exact ⟨inferInstance, inferInstance⟩

/-- The tensor product of flat objects is flat. -/
@[stacks 0G6Q "instance"]
instance tensor_isFlat (X Y : C) [IsFlat X] [IsFlat Y] : IsFlat (X ⊗ Y) := by
  constructor
  exact ObjectProperty.prop_of_iso (exactFunctor C C)
    (tensorRightTensor X Y).symm
    ⟨comp_preservesFiniteLimits _ _, comp_preservesFiniteColimits _ _⟩

/-- The tensor product of two flat objects is flat. -/
@[stacks 0G6Q]
theorem isFlat_tensor (X Y : C) [IsFlat X] [IsFlat Y] : IsFlat (X ⊗ Y) :=
  inferInstance

end CategoryTheory.MonoidalCategory
