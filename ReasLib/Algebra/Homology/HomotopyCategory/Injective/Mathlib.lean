module

public import ReasLib.Algebra.Homology.HomotopyCategory.Injective
public import Mathlib.CategoryTheory.Preadditive.Injective.InjectiveObject
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# The Mathlib Injective-Object Model

Mathlib models complexes of injectives as complexes in
`CategoryTheory.InjectiveObject`.  This leaf compares that canonical model
with the source-faithful full subcategory
`HomotopyCategory.Plus.Injective` of `K⁺(𝒜)`.
-/

open CategoryTheory
open CategoryTheory.ObjectProperty

universe v u

namespace CategoryTheory.HomotopyCategory.Plus.Injective

variable (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜]

/-- The image in `K⁺(𝒜)` of a bounded-below complex of Mathlib injective
objects has injective terms. -/
theorem fromInjectiveObject_mem
    (K : HomotopyCategory.Plus (InjectiveObject 𝒜)) :
    HomotopyCategory.Plus.termsIn 𝒜 (isInjective 𝒜)
      ((InjectiveObject.ι 𝒜).mapHomotopyCategoryPlus.obj K) := sorry

/-- Stacks 013W: the canonical comparison from Mathlib's bounded-below
homotopy category of `InjectiveObject 𝒜` to the full subcategory of
termwise-injective objects of `K⁺(𝒜)`. -/
@[stacks 013W]
noncomputable def fromInjectiveObject :
    HomotopyCategory.Plus (InjectiveObject 𝒜) ⥤ HomotopyCategory.Plus.Injective 𝒜 :=
  (HomotopyCategory.Plus.termsIn 𝒜 (isInjective 𝒜)).lift
    (InjectiveObject.ι 𝒜).mapHomotopyCategoryPlus
    (fromInjectiveObject_mem 𝒜)

/-- Forgetting the termwise-injective structure after
`fromInjectiveObject` is canonically Mathlib's homotopy-category functor
induced by `InjectiveObject.ι`. -/
@[stacks 013W]
noncomputable def fromInjectiveObjectCompιIso :
    fromInjectiveObject 𝒜 ⋙ HomotopyCategory.Plus.Injective.ι 𝒜 ≅
      (InjectiveObject.ι 𝒜).mapHomotopyCategoryPlus :=
  ObjectProperty.liftCompιIso
    (HomotopyCategory.Plus.termsIn 𝒜 (isInjective 𝒜))
    (InjectiveObject.ι 𝒜).mapHomotopyCategoryPlus
    (fromInjectiveObject_mem 𝒜)

/-- Morphisms in Mathlib's injective-object model are detected bijectively by
the canonical comparison to the termwise-injective full subcategory. -/
theorem fromInjectiveObject_map_bijective
    (X Y : HomotopyCategory.Plus (InjectiveObject 𝒜)) :
    Function.Bijective ((fromInjectiveObject 𝒜).map : (X ⟶ Y) → _) := sorry

/-- The canonical comparison from Mathlib's injective-object model admits a
fully faithful structure. The pointwise map-bijection theorem is the preferred
API because this proposition does not choose preimages. -/
theorem nonempty_fromInjectiveObject_fullyFaithful :
    Nonempty (fromInjectiveObject 𝒜).FullyFaithful := sorry

end CategoryTheory.HomotopyCategory.Plus.Injective
