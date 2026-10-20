/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.HomologicalComplex.Flat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-!
# Flat representatives in a derived category

This file owns the presentation-independent predicate that a derived object admits a
termwise-flat cochain representative supported in a prescribed interval.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u v w

namespace CategoryTheory.DerivedCategory

section

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
variable [MonoidalCategory C]

/-- The object property of admitting a termwise-flat cochain representative supported in
`[a, b]`. -/
@[stacks 08G1 "abstract flat-representative property"]
def flatRepresentativeIn (a b : ℤ) : ObjectProperty (DerivedCategory C) :=
  fun E ↦ ∃ (K : CochainComplex C ℤ) (_ : E ≅ DerivedCategory.Q.obj K),
    K.IsStrictlyGE a ∧ K.IsStrictlyLE b ∧ HomologicalComplex.IsTermwiseFlat K

/-- Object-level spelling of membership in the flat-representative property. -/
abbrev HasFlatRepresentativeIn (E : DerivedCategory C) (a b : ℤ) : Prop :=
  flatRepresentativeIn (C := C) a b E

/-- Having a flat representative in `[a, b]` unfolds to a supported termwise-flat cochain
representative. -/
theorem hasFlatRepresentativeIn_iff (E : DerivedCategory C) (a b : ℤ) :
    HasFlatRepresentativeIn E a b ↔
      ∃ (K : CochainComplex C ℤ) (_ : E ≅ DerivedCategory.Q.obj K),
        K.IsStrictlyGE a ∧ K.IsStrictlyLE b ∧ HomologicalComplex.IsTermwiseFlat K := sorry

/-- A flat-representative interval may be enlarged on either side. -/
theorem HasFlatRepresentativeIn.mono
    {E : DerivedCategory C} {a b a' b' : ℤ} (hE : HasFlatRepresentativeIn E a b)
    (ha : a' ≤ a) (hb : b ≤ b') :
    HasFlatRepresentativeIn E a' b' := sorry

/-- The existence of a flat representative in a fixed interval is invariant under isomorphism. -/
theorem HasFlatRepresentativeIn.ofIso
    {E F : DerivedCategory C} {a b : ℤ} (hE : HasFlatRepresentativeIn E a b)
    (e : E ≅ F) :
    HasFlatRepresentativeIn F a b := sorry

/-- The flat-representative property is closed under isomorphisms. -/
instance flatRepresentativeIn_isClosedUnderIsomorphisms (a b : ℤ) :
    (flatRepresentativeIn (C := C) a b).IsClosedUnderIsomorphisms := sorry

end

end CategoryTheory.DerivedCategory
