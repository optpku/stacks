/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import ReasLib.CategoryTheory.InverseSystem.Sequential

@[expose] public section

/-!
# Milnor Difference Maps for Sequential Inverse Systems

This leaf owns the product-level difference map `1 - shift` of a sequential
inverse system, the maps induced on such products, and their naturality. It is
independent of derived and triangulated categories; derived-limit constructions
can use this elementary categorical API.
-/

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u v w x

namespace CategoryTheory.SequentialInverseSystem

variable {C : Type u} [Category.{v} C]

section

variable [Preadditive C]

/-- The Milnor difference endomorphism `1 - shift` of the product of a sequential inverse
system. -/
@[stacks 08TC]
def milnorDifferenceMap (K : SequentialInverseSystem C) [HasProduct K.family] :
    ∏ᶜ K.family ⟶ ∏ᶜ K.family :=
  𝟙 _ - Pi.map' Nat.succ (fun n ↦ K.transitionMap (Nat.le_succ n))

/-- The `n`th product component of the Milnor difference map is the difference between the
`n`th projection and the successor projection followed by the transition map. -/
@[reassoc (attr := simp)]
theorem milnorDifferenceMap_comp_π (K : SequentialInverseSystem C) [HasProduct K.family]
    (n : ℕ) :
    K.milnorDifferenceMap ≫ Pi.π K.family n =
      Pi.π K.family n - Pi.π K.family (n + 1) ≫ K.transitionMap (Nat.le_succ n) := sorry

end

section SplitEpi

variable [Preadditive C]

/-- If every successor transition of a sequential inverse system is split epic, then its Milnor
difference map is split epic.  This is the reusable product-level input behind admissible Milnor
sequences. -/
@[stacks 09KR "split-epic Milnor difference map"]
theorem milnorDifferenceMap_isSplitEpi (K : SequentialInverseSystem C)
    [HasProduct K.family] (hK : ∀ n : ℕ, IsSplitEpi (K.stepMap n)) :
    IsSplitEpi K.milnorDifferenceMap := sorry

end SplitEpi

section MapSplitEpi

variable {D : Type w} [Category.{x} D] [Preadditive C] [Preadditive D]

/-- An additive functor preserving the product of a sequential inverse system sends its Milnor
difference map to a split epimorphism as soon as the images of all successor transitions are split
epic.  This form applies directly to admissibility defined by a forgetful functor. -/
@[stacks 09KR "split-epic Milnor difference map after forgetting structure"]
theorem map_milnorDifferenceMap_isSplitEpi (K : SequentialInverseSystem C)
    [HasProduct K.family] (F : C ⥤ D) [F.Additive]
    [PreservesLimit (Discrete.functor K.family) F]
    (hK : ∀ n : ℕ, IsSplitEpi (F.map (K.stepMap n))) :
    IsSplitEpi (F.map K.milnorDifferenceMap) := sorry

end MapSplitEpi

/-- The product-level map induced by a morphism of sequential inverse systems. -/
@[stacks 08TC]
noncomputable abbrev productMap {K L : SequentialInverseSystem C}
    [HasProduct K.family] [HasProduct L.family] (φ : K ⟶ L) :
    ∏ᶜ K.family ⟶ ∏ᶜ L.family :=
  Pi.lift fun n ↦ Pi.π K.family n ≫ φ.app (op n)

/-- The component of the product-level map induced by a morphism of sequential inverse systems.
-/
@[reassoc (attr := simp)]
theorem productMap_comp_π {K L : SequentialInverseSystem C}
    [HasProduct K.family] [HasProduct L.family] (φ : K ⟶ L) (n : ℕ) :
    productMap φ ≫ Pi.π L.family n = Pi.π K.family n ≫ φ.app (op n) := sorry

section

variable [Preadditive C]

/-- The Milnor difference map is natural under a morphism of sequential inverse systems. -/
@[reassoc]
theorem milnorDifferenceMap_naturality {K L : SequentialInverseSystem C}
    [HasProduct K.family] [HasProduct L.family] (φ : K ⟶ L) :
    K.milnorDifferenceMap ≫ productMap φ = productMap φ ≫ L.milnorDifferenceMap := sorry

end

end CategoryTheory.SequentialInverseSystem
