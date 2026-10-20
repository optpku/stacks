module

public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.Data.List.TFAE
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Invertible objects in a monoidal category

@stack 01CS
@stack 0FFM
@stack 0FFN
@stack 0B8K
@stack 0B8N

An object is invertible precisely when either left or right tensoring by it is an equivalence,
equivalently when it admits a two-sided tensor inverse.  The TFAE theorem is the common owner;
named pairwise equivalences keep applications independent of list indices.
-/

@[expose] public section

universe v u v' u'

namespace CategoryTheory

open MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

namespace MonoidalCategory

/-- The object property of being isomorphic to the monoidal unit. -/
@[stacks 01CS "trivial objects"]
abbrev isUnitObject : ObjectProperty C :=
  fun X ↦ Nonempty (X ≅ 𝟙_ C)

/-- Being isomorphic to the monoidal unit is invariant under isomorphism. -/
instance isUnitObject.isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms (isUnitObject (C := C)) where
  of_iso e h := by
    obtain ⟨i⟩ := h
    exact ⟨e.symm ≪≫ i⟩

/-- The monoidal unit is a unit object. -/
instance isUnitObject.unit : isUnitObject (𝟙_ C) := ⟨Iso.refl _⟩

/-- The unit-object property transports along an isomorphism. -/
theorem isUnitObject.of_iso {X Y : C} (e : X ≅ Y) (hX : isUnitObject X) :
    isUnitObject Y := by
  obtain ⟨i⟩ := hX
  exact ⟨e.symm ≪≫ i⟩

/-- The object property of tensor-invertible objects in a monoidal category. -/
@[stacks 0FFN "invertible objects", stacks 0409 "(2)", stacks 01CS "invertible"]
abbrev isInvertibleObject : ObjectProperty C :=
  fun X ↦ (tensorLeft X).IsEquivalence

namespace isInvertibleObject

private theorem leftEquivalenceOfInverse {X Y : C}
    (right : X ⊗ Y ≅ 𝟙_ C) (left : Y ⊗ X ≅ 𝟙_ C) :
    (tensorLeft X).IsEquivalence := by
  apply Functor.IsEquivalence.mk' (tensorLeft Y)
    ((leftUnitorNatIso C).symm ≪≫
      (tensoringLeft C).mapIso left.symm ≪≫ tensorLeftTensor Y X)
    ((tensorLeftTensor X Y).symm ≪≫
      (tensoringLeft C).mapIso right ≪≫ leftUnitorNatIso C)

private theorem rightEquivalenceOfInverse {X Y : C}
    (right : X ⊗ Y ≅ 𝟙_ C) (left : Y ⊗ X ≅ 𝟙_ C) :
    (tensorRight X).IsEquivalence := by
  apply Functor.IsEquivalence.mk' (tensorRight Y)
    ((rightUnitorNatIso C).symm ≪≫
      (tensoringRight C).mapIso right.symm ≪≫ tensorRightTensor X Y)
    ((tensorRightTensor Y X).symm ≪≫
      (tensoringRight C).mapIso left ≪≫ rightUnitorNatIso C)

private theorem existsInverseOfLeft (X : C)
    (h : (tensorLeft X).IsEquivalence) :
    ∃ Y : C, Nonempty (X ⊗ Y ≅ 𝟙_ C) ∧ Nonempty (Y ⊗ X ≅ 𝟙_ C) := by
  -- Local instance justification (proof-local temporary data): the supplied equivalence is needed to access its inverse and unit/counit isomorphisms.
  letI := h
  let Y := (tensorLeft X).asEquivalence.inverse.obj (𝟙_ C)
  let right : X ⊗ Y ≅ 𝟙_ C :=
    (tensorLeft X).asEquivalence.counitIso.app (𝟙_ C)
  let e : (tensorLeft X).obj (Y ⊗ X) ≅ (tensorLeft X).obj (𝟙_ C) :=
    (α_ X Y X).symm ≪≫ (right ⊗ᵢ Iso.refl X) ≪≫
      λ_ X ≪≫ (ρ_ X).symm
  let left : Y ⊗ X ≅ 𝟙_ C :=
    (tensorLeft X).asEquivalence.unitIso.app (Y ⊗ X) ≪≫
      (tensorLeft X).asEquivalence.inverse.mapIso e ≪≫
        ((tensorLeft X).asEquivalence.unitIso.app (𝟙_ C)).symm
  exact ⟨Y, ⟨right⟩, ⟨left⟩⟩

private theorem existsInverseOfRight (X : C)
    (h : (tensorRight X).IsEquivalence) :
    ∃ Y : C, Nonempty (X ⊗ Y ≅ 𝟙_ C) ∧ Nonempty (Y ⊗ X ≅ 𝟙_ C) := by
  -- Local instance justification (proof-local temporary data): the supplied equivalence is needed to access its inverse and unit/counit isomorphisms.
  letI := h
  let Y := (tensorRight X).asEquivalence.inverse.obj (𝟙_ C)
  let left : Y ⊗ X ≅ 𝟙_ C :=
    (tensorRight X).asEquivalence.counitIso.app (𝟙_ C)
  let e : (tensorRight X).obj (X ⊗ Y) ≅ (tensorRight X).obj (𝟙_ C) :=
    α_ X Y X ≪≫ (Iso.refl X ⊗ᵢ left) ≪≫
      ρ_ X ≪≫ (λ_ X).symm
  let right : X ⊗ Y ≅ 𝟙_ C :=
    (tensorRight X).asEquivalence.unitIso.app (X ⊗ Y) ≪≫
      (tensorRight X).asEquivalence.inverse.mapIso e ≪≫
        ((tensorRight X).asEquivalence.unitIso.app (𝟙_ C)).symm
  exact ⟨Y, ⟨right⟩, ⟨left⟩⟩

/-- Left tensoring by `X`, right tensoring by `X`, and existence of a two-sided tensor inverse
for `X` are equivalent. -/
@[stacks 0FFM "equivalent tensor-invertibility criteria"]
theorem tfae (X : C) :
    List.TFAE [
      (tensorLeft X).IsEquivalence,
      (tensorRight X).IsEquivalence,
      ∃ X' : C, Nonempty (X ⊗ X' ≅ 𝟙_ C) ∧ Nonempty (X' ⊗ X ≅ 𝟙_ C)
    ] := by
  tfae_have 1 → 3 := existsInverseOfLeft X
  tfae_have 2 → 3 := existsInverseOfRight X
  tfae_have 3 → 1 := by
    rintro ⟨Y, ⟨right⟩, ⟨left⟩⟩
    exact leftEquivalenceOfInverse right left
  tfae_have 3 → 2 := by
    rintro ⟨Y, ⟨right⟩, ⟨left⟩⟩
    exact rightEquivalenceOfInverse right left
  tfae_finish

/-- Left tensoring by `X` is an equivalence if and only if right tensoring by `X` is an
equivalence. -/
@[stacks 0FFM "left-right tensor equivalence"]
theorem iff_tensorRight (X : C) :
    (tensorLeft X).IsEquivalence ↔ (tensorRight X).IsEquivalence :=
  (tfae X).out 0 1

/-- Left tensoring by `X` is an equivalence if and only if `X` admits a two-sided tensor
inverse. -/
@[stacks 0FFM "left tensor equivalence and two-sided inverse"]
theorem iff_exists_tensorInverse (X : C) :
    (tensorLeft X).IsEquivalence ↔
      ∃ X' : C, Nonempty (X ⊗ X' ≅ 𝟙_ C) ∧ Nonempty (X' ⊗ X ≅ 𝟙_ C) :=
  (tfae X).out 0 2

/-- Right tensoring by `X` is an equivalence if and only if `X` admits a two-sided tensor
inverse. -/
@[stacks 0FFM "right tensor equivalence and two-sided inverse"]
theorem tensorRight_iff_exists_tensorInverse (X : C) :
    (tensorRight X).IsEquivalence ↔
      ∃ X' : C, Nonempty (X ⊗ X' ≅ 𝟙_ C) ∧ Nonempty (X' ⊗ X ≅ 𝟙_ C) :=
  (tfae X).out 1 2

/-- In a braided monoidal category, right tensoring by `X` is an equivalence exactly when `X`
admits a right tensor inverse; the braiding supplies the inverse in the other order. -/
@[stacks 0B8N "(1)"]
theorem tensorRight_iff_exists_rightTensorInverse [BraidedCategory C] (X : C) :
    (tensorRight X).IsEquivalence ↔
      ∃ X' : C, Nonempty (X ⊗ X' ≅ 𝟙_ C) := by
  refine (tensorRight_iff_exists_tensorInverse X).trans ?_
  constructor
  · rintro ⟨Y, right, _⟩
    exact ⟨Y, right⟩
  · rintro ⟨Y, ⟨right⟩⟩
    exact ⟨Y, ⟨right⟩, ⟨β_ Y X ≪≫ right⟩⟩

/-- In a braided monoidal category, a canonically invertible object is equivalently an object
admitting a right tensor inverse. -/
@[stacks 0B8K "(1) iff (2)", stacks 0B8N "(1)"]
theorem iff_exists_rightTensorInverse [BraidedCategory C] (X : C) :
    isInvertibleObject X ↔
      ∃ X' : C, Nonempty (X ⊗ X' ≅ 𝟙_ C) := by
  refine (iff_exists_tensorInverse X).trans ?_
  constructor
  · rintro ⟨Y, right, _⟩
    exact ⟨Y, right⟩
  · rintro ⟨Y, ⟨right⟩⟩
    exact ⟨Y, ⟨right⟩, ⟨β_ Y X ≪≫ right⟩⟩

/-- The canonical invertible-object property automatically supplies equivalence of right
tensoring. -/
instance tensorRightIsEquivalence (X : C) [isInvertibleObject X] :
    (tensorRight X).IsEquivalence :=
  (iff_tensorRight X).mp (inferInstance : isInvertibleObject X)

/-- Right-tensor equivalence implies the canonical invertible-object property. This is an
explicit bridge rather than an instance, so typeclass search has a single canonical direction. -/
@[stacks 0FFM "right-tensor bridge"]
theorem ofTensorRight (X : C) (hX : (tensorRight X).IsEquivalence) :
    isInvertibleObject X :=
  (iff_tensorRight X).mpr hX

/-- A chosen tensor inverse of an invertible object. -/
@[stacks 0FFN "chosen inverse"]
noncomputable def inverse (X : C) [isInvertibleObject X] : C :=
  (tensorLeft X).asEquivalence.inverse.obj (𝟙_ C)

/-- The canonical comparison from an invertible object tensored with its chosen inverse to the
monoidal unit. -/
@[stacks 0FFN "right inverse comparison"]
noncomputable def tensorInverseIso (X : C) [isInvertibleObject X] :
    X ⊗ inverse X ≅ 𝟙_ C :=
  (tensorLeft X).asEquivalence.counitIso.app (𝟙_ C)

/-- The canonical comparison from the chosen inverse tensored with the original object to the
monoidal unit. -/
@[stacks 0FFN "left inverse comparison"]
noncomputable def inverseTensorIso (X : C) [isInvertibleObject X] :
    inverse X ⊗ X ≅ 𝟙_ C :=
  let e : (tensorLeft X).obj (inverse X ⊗ X) ≅ (tensorLeft X).obj (𝟙_ C) :=
    (α_ X (inverse X) X).symm ≪≫
      (tensorInverseIso X ⊗ᵢ Iso.refl X) ≪≫ (λ_ X) ≪≫ (ρ_ X).symm
  (tensorLeft X).asEquivalence.unitIso.app (inverse X ⊗ X) ≪≫
    (tensorLeft X).asEquivalence.inverse.mapIso e ≪≫
      ((tensorLeft X).asEquivalence.unitIso.app (𝟙_ C)).symm

/-- The chosen tensor inverse is itself tensor-invertible. -/
instance inverseIsInvertible (X : C) [isInvertibleObject X] :
    isInvertibleObject (inverse X) :=
  leftEquivalenceOfInverse (inverseTensorIso X) (tensorInverseIso X)

/-- Tensor-invertible objects contain the unit and are closed under tensor products. -/
instance isMonoidal : ObjectProperty.IsMonoidal (isInvertibleObject (C := C)) where
  prop_unit :=
    Functor.isEquivalence_of_iso (leftUnitorNatIso C).symm
  prop_tensor X Y hX hY := by
    -- Local instance justification (proof-local temporary data): the two supplied object-property proofs are consumed as equivalence instances for tensoring.
    letI := hX
    -- Local instance justification (proof-local temporary data): the two supplied object-property proofs are consumed as equivalence instances for tensoring.
    letI := hY
    exact Functor.isEquivalence_of_iso (tensorLeftTensor X Y).symm

/-- Tensor-invertibility is invariant under isomorphism. -/
instance isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms (isInvertibleObject (C := C)) where
  of_iso e hX := by
    -- Local instance justification (proof-local temporary data): the supplied invertibility proof is required to transport the tensor-left equivalence across `e`.
    letI := hX
    exact Functor.isEquivalence_of_iso ((tensoringLeft C).mapIso e)

/-- The monoidal unit is tensor-invertible. -/
instance unit : isInvertibleObject (𝟙_ C) :=
  ObjectProperty.prop_unit (isInvertibleObject (C := C))

/-- Every object isomorphic to the monoidal unit is tensor-invertible. -/
instance ofIsUnitObject (X : C) [isUnitObject X] : isInvertibleObject X := by
  obtain ⟨e⟩ := ‹isUnitObject X›
  exact ObjectProperty.prop_of_iso isInvertibleObject e.symm
    (inferInstance : isInvertibleObject (𝟙_ C))

/-- A tensor product of tensor-invertible objects is tensor-invertible. -/
@[stacks 040A "(1), categorical generality", stacks 01CT "(1), categorical generality"]
instance tensor (X Y : C) [isInvertibleObject X] [isInvertibleObject Y] :
    isInvertibleObject (X ⊗ Y) :=
  ObjectProperty.prop_tensor
    (inferInstance : isInvertibleObject X)
    (inferInstance : isInvertibleObject Y)

/-- Tensor-invertibility transports along an isomorphism. -/
theorem of_iso {X Y : C} (e : X ≅ Y) (hX : isInvertibleObject X) :
    isInvertibleObject Y :=
  ObjectProperty.prop_of_iso isInvertibleObject e hX

/-- A monoidal functor sends tensor-invertible objects to tensor-invertible objects. -/
@[stacks 0FFN "monoidal-functor preservation"]
instance map {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
    (F : C ⥤ D) [F.Monoidal] (X : C) [isInvertibleObject X] :
    isInvertibleObject (F.obj X) :=
  leftEquivalenceOfInverse
    (Functor.Monoidal.μIso F X (inverse X) ≪≫
      F.mapIso (tensorInverseIso X) ≪≫
        (Functor.Monoidal.εIso F).symm)
    (Functor.Monoidal.μIso F (inverse X) X ≪≫
      F.mapIso (inverseTensorIso X) ≪≫
        (Functor.Monoidal.εIso F).symm)

end isInvertibleObject
end MonoidalCategory

end CategoryTheory
