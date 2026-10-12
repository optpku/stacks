/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.ObjectProperty.CompleteLattice
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import ReasLib.Algebra.Homology.CochainComplex.Projective.Bounded
import Mathlib.Tactic.CrossRefAttribute

/-!
# Projective amplitude in a derived category

Projective amplitude is an isomorphism-stable object property of an arbitrary derived category.  The
source-facing representative formulation remains explicit, while the companion bundled statement
uses `CochainComplex.ProjectiveIn` so later constructions inherit support and projectivity
automatically.
@stack 0A5N
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w v u

namespace CategoryTheory.DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- Definition 15.69.1 (2), abstract form: a derived object represented by projectives supported
in `[a, b]`. -/
@[stacks 0A5N "projective amplitude in a fixed interval"]
def projectiveAmplitudeIn (a b : ℤ) : ObjectProperty (DerivedCategory C) :=
  fun K ↦ ∃ (P : CochainComplex C ℤ) (_ : K ≅ DerivedCategory.Q.obj P),
    P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧ ∀ i : ℤ, Projective (P.X i)

/-- Object-level spelling of membership in a fixed projective-amplitude interval. -/
@[stacks 0A5N "object-level projective amplitude"]
abbrev HasProjectiveAmplitudeIn (K : DerivedCategory C) (a b : ℤ) : Prop :=
  projectiveAmplitudeIn (C := C) a b K

/-- Definition 15.69.1 (1), abstract form: objects with projective amplitude in some finite
interval. -/
@[stacks 0A5N "finite projective dimension"]
def finiteProjectiveDimension : ObjectProperty (DerivedCategory C) :=
  ⨆ a : ℤ, ⨆ b : ℤ, projectiveAmplitudeIn (C := C) a b

/-- Object-level spelling of the finite-projective-dimension property. -/
@[stacks 0A5N "object-level finite projective dimension"]
abbrev HasFiniteProjectiveDimension (K : DerivedCategory C) : Prop :=
  finiteProjectiveDimension (C := C) K

/-- Projective amplitude may be unpacked to an ordinary cochain complex with explicit support and
termwise projectivity. -/
@[stacks 0A5N "projective amplitude representative bridge"]
theorem hasProjectiveAmplitudeIn_iff_exists_representative
    (K : DerivedCategory C) (a b : ℤ) :
    HasProjectiveAmplitudeIn K a b ↔
      ∃ (P : CochainComplex C ℤ) (_ : K ≅ DerivedCategory.Q.obj P),
        P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧ ∀ i : ℤ, Projective (P.X i) := sorry

/-- Projective amplitude is equivalently witnessed by the bundled representative owner. -/
@[stacks 0A5N "bundled projective amplitude bridge"]
theorem hasProjectiveAmplitudeIn_iff_exists_bundled
    (K : DerivedCategory C) (a b : ℤ) :
    HasProjectiveAmplitudeIn K a b ↔
      ∃ (P : CochainComplex.ProjectiveIn C a b),
        Nonempty (K ≅ DerivedCategory.Q.obj P.obj) := sorry

/-- A projective-amplitude interval may be enlarged on either side. -/
@[stacks 0A5N "monotonicity of projective amplitude"]
theorem HasProjectiveAmplitudeIn.mono
    {K : DerivedCategory C} {a b a' b' : ℤ} (hK : HasProjectiveAmplitudeIn K a b)
    (ha : a' ≤ a) (hb : b ≤ b') :
    HasProjectiveAmplitudeIn K a' b' := sorry

/-- Projective amplitude is preserved when the represented derived object is replaced by an
isomorphic object. -/
@[stacks 0A5N "isomorphism invariance of projective amplitude"]
theorem HasProjectiveAmplitudeIn.ofIso
    {K L : DerivedCategory C} {a b : ℤ} (hK : HasProjectiveAmplitudeIn K a b)
    (e : K ≅ L) : HasProjectiveAmplitudeIn L a b := sorry

/-- Projective amplitude in `[a, b]` places the object in `D^{≥ a}`. -/
@[stacks 0A5N "lower t-structure bound from projective amplitude"]
theorem HasProjectiveAmplitudeIn.isGE
    {K : DerivedCategory C} {a b : ℤ} (hK : HasProjectiveAmplitudeIn K a b) :
    K.IsGE a := sorry

/-- Projective amplitude in `[a, b]` places the object in `D^{≤ b}`. -/
@[stacks 0A5N "upper t-structure bound from projective amplitude"]
theorem HasProjectiveAmplitudeIn.isLE
    {K : DerivedCategory C} {a b : ℤ} (hK : HasProjectiveAmplitudeIn K a b) :
    K.IsLE b := sorry

/-- Fixed projective amplitude is an isomorphism-closed object property. -/
@[stacks 0A5N "isomorphism stability of projective amplitude"]
instance projectiveAmplitudeIn_isClosedUnderIsomorphisms (a b : ℤ) :
    (projectiveAmplitudeIn (C := C) a b).IsClosedUnderIsomorphisms := sorry

/-- Finite projective dimension is equivalent to membership in one finite projective-amplitude
interval. -/
@[stacks 0A5N "finite projective dimension interval bridge"]
theorem hasFiniteProjectiveDimension_iff (K : DerivedCategory C) :
    HasFiniteProjectiveDimension K ↔
      ∃ a b : ℤ, HasProjectiveAmplitudeIn K a b := sorry

/-- A fixed projective-amplitude interval gives finite projective dimension. -/
@[stacks 0A5N "finite projective dimension from an interval"]
theorem HasProjectiveAmplitudeIn.hasFiniteProjectiveDimension
    {K : DerivedCategory C} {a b : ℤ} (hK : HasProjectiveAmplitudeIn K a b) :
    HasFiniteProjectiveDimension K := sorry

/-- Finite projective dimension is preserved by isomorphisms in the derived category. -/
@[stacks 0A5N "isomorphism invariance of finite projective dimension"]
theorem HasFiniteProjectiveDimension.ofIso
    {K L : DerivedCategory C} (hK : HasFiniteProjectiveDimension K) (e : K ≅ L) :
    HasFiniteProjectiveDimension L := sorry

/-- Finite projective dimension is an isomorphism-closed object property. -/
@[stacks 0A5N "isomorphism stability of finite projective dimension"]
instance finiteProjectiveDimension_isClosedUnderIsomorphisms :
    (finiteProjectiveDimension (C := C)).IsClosedUnderIsomorphisms := sorry

end CategoryTheory.DerivedCategory
