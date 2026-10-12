/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.KFlat
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.FlatRepresentative

/-!
# Lower-bounded K-flat representatives in a derived category

This leaf adds the K-flat lower-bounded presentation predicate to the interval-only flat
representative core.  Consumers of finite intervals therefore do not inherit K-flat machinery.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u v w

namespace CategoryTheory.DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
variable [MonoidalCategory C]
variable [MonoidalPreadditive C]
variable [(curriedTensor C).Additive]
variable [∀ X : C, ((curriedTensor C).obj X).Additive]

/-- The object property of admitting a K-flat, termwise-flat cochain representative supported
in degrees `≥ a`. -/
@[stacks 0F1M "abstract lower-bounded flat representative property"]
def flatRepresentativeGE (a : ℤ) : ObjectProperty (DerivedCategory C) :=
  fun E ↦ ∃ (K : CochainComplex C ℤ) (_ : E ≅ DerivedCategory.Q.obj K),
    K.IsStrictlyGE a ∧ K.IsKFlat ∧ HomologicalComplex.IsTermwiseFlat K

/-- Object-level spelling of membership in the lower-bounded flat-representative property. -/
abbrev HasFlatRepresentativeGE (E : DerivedCategory C) (a : ℤ) : Prop :=
  flatRepresentativeGE (C := C) a E

/-- Having a lower-bounded flat representative unfolds to a supported K-flat, termwise-flat
cochain representative. -/
theorem hasFlatRepresentativeGE_iff (E : DerivedCategory C) (a : ℤ) :
    HasFlatRepresentativeGE E a ↔
      ∃ (K : CochainComplex C ℤ) (_ : E ≅ DerivedCategory.Q.obj K),
        K.IsStrictlyGE a ∧ K.IsKFlat ∧ HomologicalComplex.IsTermwiseFlat K := sorry

/-- A lower-bounded flat representative remains valid after lowering the bound. -/
theorem HasFlatRepresentativeGE.mono
    {E : DerivedCategory C} {a a' : ℤ} (hE : HasFlatRepresentativeGE E a)
    (ha : a' ≤ a) :
    HasFlatRepresentativeGE E a' := sorry

/-- The existence of a lower-bounded flat representative is invariant under isomorphism. -/
theorem HasFlatRepresentativeGE.ofIso
    {E F : DerivedCategory C} {a : ℤ} (hE : HasFlatRepresentativeGE E a)
    (e : E ≅ F) :
    HasFlatRepresentativeGE F a := sorry

/-- The lower-bounded flat-representative property is closed under isomorphisms. -/
instance flatRepresentativeGE_isClosedUnderIsomorphisms (a : ℤ) :
    (flatRepresentativeGE (C := C) a).IsClosedUnderIsomorphisms := sorry

end CategoryTheory.DerivedCategory
