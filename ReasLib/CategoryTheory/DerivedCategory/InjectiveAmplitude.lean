/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import ReasLib.Algebra.Homology.CochainComplex.Injective.Bounded
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Injective amplitude in a derived category

@stack 0A5S

Injective amplitude is owned here as an isomorphism-stable object property of an arbitrary
derived category.  A witness is a bundled cochain complex whose support bounds and termwise
injectivity are available canonically from its type.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w v u

namespace CategoryTheory.DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- The object property of being represented by a complex of injectives supported in `[a, b]`. -/
@[stacks 0A5S "(2), abstract derived-category form"]
def injectiveAmplitudeIn (a b : ℤ) : ObjectProperty (DerivedCategory C) :=
  fun K ↦ ∃ I : CochainComplex.InjectiveIn C a b,
    Nonempty (K ≅ DerivedCategory.Q.obj I.obj)

/-- Object-level spelling of membership in a fixed injective-amplitude interval. -/
abbrev HasInjectiveAmplitudeIn (K : DerivedCategory C) (a b : ℤ) : Prop :=
  injectiveAmplitudeIn (C := C) a b K

/-- The object property of having injective amplitude in some finite interval. -/
@[stacks 0A5S "(1), abstract derived-category form"]
def finiteInjectiveDimension : ObjectProperty (DerivedCategory C) :=
  ⨆ a : ℤ, ⨆ b : ℤ, injectiveAmplitudeIn (C := C) a b

/-- Object-level spelling of membership in the finite-injective-dimension property. -/
abbrev HasFiniteInjectiveDimension (K : DerivedCategory C) : Prop :=
  finiteInjectiveDimension (C := C) K

/-- Injective amplitude is exactly the existence of a bundled representative in the specified
interval. -/
theorem hasInjectiveAmplitudeIn_iff_exists_representative
    (K : DerivedCategory C) (a b : ℤ) :
    HasInjectiveAmplitudeIn K a b ↔
      ∃ I : CochainComplex.InjectiveIn C a b,
        Nonempty (K ≅ DerivedCategory.Q.obj I.obj) := sorry

/-- Injective amplitude may be unpacked to an ordinary cochain complex with explicit support and
injectivity conditions. -/
theorem hasInjectiveAmplitudeIn_iff_exists_complex
    (K : DerivedCategory C) (a b : ℤ) :
    HasInjectiveAmplitudeIn K a b ↔
      ∃ I : CochainComplex C ℤ,
        I.IsStrictlyGE a ∧ I.IsStrictlyLE b ∧
          (∀ i : ℤ, Injective (I.X i)) ∧ Nonempty (K ≅ DerivedCategory.Q.obj I) := sorry

/-- An injective-amplitude interval may be enlarged on either side. -/
theorem HasInjectiveAmplitudeIn.mono
    {K : DerivedCategory C} {a b a' b' : ℤ} (hK : HasInjectiveAmplitudeIn K a b)
    (ha : a' ≤ a) (hb : b ≤ b') :
    HasInjectiveAmplitudeIn K a' b' := sorry

/-- Injective amplitude is preserved when the represented derived object is replaced by an
isomorphic object. -/
theorem HasInjectiveAmplitudeIn.ofIso
    {K L : DerivedCategory C} {a b : ℤ} (hK : HasInjectiveAmplitudeIn K a b)
    (e : K ≅ L) : HasInjectiveAmplitudeIn L a b := sorry

/-- Injective amplitude in `[a, b]` places the object in `D^{≥ a}`. -/
theorem HasInjectiveAmplitudeIn.isGE
    {K : DerivedCategory C} {a b : ℤ} (hK : HasInjectiveAmplitudeIn K a b) :
    K.IsGE a := sorry

/-- Injective amplitude in `[a, b]` places the object in `D^{≤ b}`. -/
theorem HasInjectiveAmplitudeIn.isLE
    {K : DerivedCategory C} {a b : ℤ} (hK : HasInjectiveAmplitudeIn K a b) :
    K.IsLE b := sorry

/-- Fixed injective amplitude is an isomorphism-closed object property. -/
instance injectiveAmplitudeIn_isClosedUnderIsomorphisms (a b : ℤ) :
    (injectiveAmplitudeIn (C := C) a b).IsClosedUnderIsomorphisms := sorry

/-- Finite injective dimension is equivalent to membership in one finite injective-amplitude
interval. -/
theorem hasFiniteInjectiveDimension_iff (K : DerivedCategory C) :
    HasFiniteInjectiveDimension K ↔
      ∃ a b : ℤ, HasInjectiveAmplitudeIn K a b := sorry

/-- A fixed injective-amplitude interval gives finite injective dimension. -/
theorem HasInjectiveAmplitudeIn.hasFiniteInjectiveDimension
    {K : DerivedCategory C} {a b : ℤ} (hK : HasInjectiveAmplitudeIn K a b) :
    HasFiniteInjectiveDimension K := sorry

/-- Finite injective dimension is preserved by isomorphisms in the derived category. -/
theorem HasFiniteInjectiveDimension.ofIso
    {K L : DerivedCategory C} (hK : HasFiniteInjectiveDimension K) (e : K ≅ L) :
    HasFiniteInjectiveDimension L := sorry

/-- Finite injective dimension is an isomorphism-closed object property. -/
instance finiteInjectiveDimension_isClosedUnderIsomorphisms :
    (finiteInjectiveDimension (C := C)).IsClosedUnderIsomorphisms := sorry

end CategoryTheory.DerivedCategory
