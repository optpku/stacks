/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Bounded
public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.Algebra.Homology.HomotopyCategory.Plus
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Bounded Homotopy Categories

@stack 013H

For a preadditive category `A`, this leaf defines the bounded-above and bounded homotopy
categories as full subcategories of `HomotopyCategory A (up Z)` and exposes their canonical
inclusions and quotient bridges. Mathlib's bounded-below owner `HomotopyCategory.Plus` is reused
directly.
-/

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open ComplexShape

universe v u

namespace CategoryTheory

scoped notation "Comp(" A:arg ")" => CochainComplex A ℤ
scoped notation "Comp⁺(" A:arg ")" => CochainComplex.Plus A
scoped notation "Comp⁻(" A:arg ")" => CochainComplex.Minus A
scoped notation "Compᵇ(" A:arg ")" => CochainComplex.Bounded A
scoped notation "K(" A:arg ")" => HomotopyCategory A (up ℤ)

variable {𝒜 : Type u} [Category.{v} 𝒜] [Preadditive 𝒜]

section

variable (𝒜)

namespace HomotopyCategory

/-- The bounded-above owner on `K(𝒜)`. -/
@[stacks 013H "bounded-above homotopy objects"]
protected def minus : ObjectProperty (K(𝒜)) :=
  fun K ↦ CochainComplex.minus 𝒜 K.as

/-- Membership in the bounded-above homotopy-category owner is boundedness of the underlying
complex. -/
lemma minus_iff (K : K(𝒜)) :
    HomotopyCategory.minus 𝒜 K ↔ CochainComplex.minus 𝒜 K.as := Iff.rfl

/-- Bounded-above homotopy objects are stable under cohomological shifts. -/
@[stacks 013H "bounded-above homotopy objects are stable under shifts"]
instance : (HomotopyCategory.minus 𝒜).IsStableUnderShift ℤ := sorry

/-- The bounded-above homotopy objects form a triangulated subcategory. -/
@[stacks 013H "bounded-above homotopy objects form a triangulated subcategory"]
instance [HasZeroObject 𝒜] [HasBinaryBiproducts 𝒜] :
    (HomotopyCategory.minus 𝒜).IsTriangulated := sorry

/-- The bounded-above homotopy owner contains a zero object. -/
@[stacks 013H "bounded-above homotopy objects contain zero"]
instance [HasZeroObject 𝒜] : (HomotopyCategory.minus 𝒜).ContainsZero where
  exists_zero := by
    refine ⟨(HomotopyCategory.quotient 𝒜 (up ℤ)).obj (HomologicalComplex.zero : Comp(𝒜)), ?_, ?_⟩
    · exact (HomotopyCategory.quotient 𝒜 (up ℤ)).map_isZero HomologicalComplex.isZero_zero
    · simpa [HomotopyCategory.minus, HomotopyCategory.quotient_obj_as] using
        CochainComplex.zero_mem_minus 𝒜

/-- The bounded owner on `K(𝒜)`. -/
@[stacks 013H "bounded homotopy objects"]
protected def bounded : ObjectProperty (K(𝒜)) :=
  fun K ↦ CochainComplex.bounded 𝒜 K.as

/-- Membership in the bounded homotopy-category owner is boundedness of the underlying complex. -/
lemma bounded_iff (K : K(𝒜)) :
    HomotopyCategory.bounded 𝒜 K ↔ CochainComplex.bounded 𝒜 K.as := Iff.rfl

/-- Bounded homotopy objects are stable under cohomological shifts. -/
@[stacks 013H "bounded homotopy objects are stable under shifts"]
instance : (HomotopyCategory.bounded 𝒜).IsStableUnderShift ℤ := sorry

/-- The bounded homotopy objects form a triangulated subcategory. -/
@[stacks 013H "bounded homotopy objects form a triangulated subcategory"]
instance [HasZeroObject 𝒜] [HasBinaryBiproducts 𝒜] :
    (HomotopyCategory.bounded 𝒜).IsTriangulated := sorry

/-- The bounded homotopy owner contains a zero object. -/
@[stacks 013H "bounded homotopy objects contain zero"]
instance [HasZeroObject 𝒜] : (HomotopyCategory.bounded 𝒜).ContainsZero where
  exists_zero := by
    refine ⟨(HomotopyCategory.quotient 𝒜 (up ℤ)).obj (HomologicalComplex.zero : Comp(𝒜)), ?_, ?_⟩
    · exact (HomotopyCategory.quotient 𝒜 (up ℤ)).map_isZero HomologicalComplex.isZero_zero
    · simpa [HomotopyCategory.bounded, HomotopyCategory.quotient_obj_as] using
        CochainComplex.zero_mem_bounded 𝒜

/-- The bounded-above homotopy category `K⁻(𝒜)`. -/
@[stacks 013H "bounded-above homotopy category"]
abbrev Minus :=
  (HomotopyCategory.minus 𝒜).FullSubcategory

namespace Minus

/-- The inclusion `K⁻(𝒜) ⥤ K(𝒜)`. -/
@[stacks 013H "inclusion of the bounded-above homotopy category"]
abbrev ι : HomotopyCategory.Minus 𝒜 ⥤ K(𝒜) :=
  (HomotopyCategory.minus 𝒜).ι

/-- The canonical inclusion `K⁻(𝒜) ⥤ K(𝒜)` is fully faithful. -/
@[stacks 013H "full faithfulness of the bounded-above homotopy inclusion"]
abbrev fullyFaithfulι : (ι 𝒜).FullyFaithful :=
  ObjectProperty.fullyFaithfulι _

end Minus

/-- The bounded homotopy category `Kᵇ(𝒜)`. -/
@[stacks 013H "bounded homotopy category"]
abbrev Bounded :=
  (HomotopyCategory.bounded 𝒜).FullSubcategory

namespace Bounded

/-- The inclusion `Kᵇ(𝒜) ⥤ K(𝒜)`. -/
@[stacks 013H "inclusion of the bounded homotopy category"]
abbrev ι : HomotopyCategory.Bounded 𝒜 ⥤ K(𝒜) :=
  (HomotopyCategory.bounded 𝒜).ι

/-- The canonical inclusion `Kᵇ(𝒜) ⥤ K(𝒜)` is fully faithful. -/
@[stacks 013H "full faithfulness of the bounded homotopy inclusion"]
abbrev fullyFaithfulι : (ι 𝒜).FullyFaithful :=
  ObjectProperty.fullyFaithfulι _

end Bounded

end HomotopyCategory

scoped notation "K⁺(" A:arg ")" => HomotopyCategory.Plus A
scoped notation "K⁻(" A:arg ")" => HomotopyCategory.Minus A
scoped notation "Kᵇ(" A:arg ")" => HomotopyCategory.Bounded A

end

end CategoryTheory


