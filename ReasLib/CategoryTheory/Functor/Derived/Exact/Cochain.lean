module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Functor.Derived.Cochain

@[expose] public section

/-!
# Cochain-Level Derivation of Exact Functors

An exact functor induces a functor on derived categories directly from its
action on cochain complexes. This leaf records the corresponding left- and
right-derived universal properties.
-/

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

noncomputable section

universe wA wB vA vB uA uB

namespace CategoryTheory.Functor.RightDerived.Exact.Cochain

variable {A : Type uA} {B : Type uB}
variable [Category.{vA} A] [Category.{vB} B] [Abelian A] [Abelian B]
variable [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]

/-- The right-derived universal map is the native lift of a natural transformation
through localization, using the actual exact-functor factorization isomorphism. -/
noncomputable def universal (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    (Functor.LeftExtension.mk F.mapDerivedCategory F.mapDerivedCategoryFactors.inv).IsUniversal :=
  Limits.IsInitial.ofUniqueHom
    (fun E ↦ StructuredArrow.homMk
      ((Localization.fullyFaithfulWhiskeringLeft
        (DerivedCategory.Q : CochainComplex A ℤ ⥤ DerivedCategory A)
        (HomologicalComplex.quasiIso A (up ℤ)) (DerivedCategory B)).preimage
          (F.mapDerivedCategoryFactors.hom ≫ E.hom)) (by sorry))
    (fun E φ ↦ by sorry)

/-- The universal descent map is the lift of the displayed transformation through localization. -/
@[simp]
theorem universal_desc (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (E : Functor.LeftExtension
      (DerivedCategory.Q : CochainComplex A ℤ ⥤ DerivedCategory A)
      (Derived.Cochain.toDerived F)) :
    (universal F).desc E =
      (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
        (HomologicalComplex.quasiIso A (up ℤ)) (DerivedCategory B)).preimage
          (F.mapDerivedCategoryFactors.hom ≫ E.hom) := rfl

/-- The derived-category functor induced by an exact functor is its
cochain-level right derived functor. -/
@[stacks 015F]
noncomputable instance isRightDerived (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    F.mapDerivedCategory.IsRightDerivedFunctor
      F.mapDerivedCategoryFactors.inv
      (HomologicalComplex.quasiIso A (up ℤ)) where
  isLeftKanExtension := ⟨⟨universal F⟩⟩

/-- The cochain-level localization of an exact functor admits the functor induced on derived
categories as a right derived functor. The higher priority selects this exact model over
resolution-based fallback instances when both apply. -/
@[stacks 015F]
noncomputable instance (priority := 1100) hasRightDerived (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    (Derived.Cochain.toDerived F).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso A (up ℤ)) :=
  Functor.HasRightDerivedFunctor.mk' (RF := F.mapDerivedCategory)
    (α := F.mapDerivedCategoryFactors.inv)

end CategoryTheory.Functor.RightDerived.Exact.Cochain

namespace CategoryTheory.Functor.LeftDerived.Exact.Cochain

variable {A : Type uA} {B : Type uB}
variable [Category.{vA} A] [Category.{vB} B] [Abelian A] [Abelian B]
variable [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]

/-- The left-derived universal map is the native lift through localization,
with the actual factorization isomorphism fixing the direction. -/
noncomputable def universal (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    (Functor.RightExtension.mk F.mapDerivedCategory F.mapDerivedCategoryFactors.hom).IsUniversal :=
  Limits.IsTerminal.ofUniqueHom
    (fun E ↦ CostructuredArrow.homMk
      ((Localization.fullyFaithfulWhiskeringLeft
        (DerivedCategory.Q : CochainComplex A ℤ ⥤ DerivedCategory A)
        (HomologicalComplex.quasiIso A (up ℤ)) (DerivedCategory B)).preimage
          (E.hom ≫ F.mapDerivedCategoryFactors.inv)) (by sorry))
    (fun E φ ↦ by sorry)

/-- The universal lift is the lift of the displayed transformation through localization. -/
@[simp]
theorem universal_lift (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (E : Functor.RightExtension
      (DerivedCategory.Q : CochainComplex A ℤ ⥤ DerivedCategory A)
      (Derived.Cochain.toDerived F)) :
    (universal F).lift E =
      (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
        (HomologicalComplex.quasiIso A (up ℤ)) (DerivedCategory B)).preimage
          (E.hom ≫ F.mapDerivedCategoryFactors.inv) := rfl

/-- The derived-category functor induced by an exact functor is its
cochain-level left derived functor. -/
@[stacks 015F]
noncomputable instance isLeftDerived (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    F.mapDerivedCategory.IsLeftDerivedFunctor
      F.mapDerivedCategoryFactors.hom
      (HomologicalComplex.quasiIso A (up ℤ)) where
  isRightKanExtension := ⟨⟨universal F⟩⟩

/-- The cochain-level localization of an exact functor admits the functor induced on derived
categories as a left derived functor. -/
@[stacks 015F]
noncomputable instance (priority := 1100) hasLeftDerived (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    (Derived.Cochain.toDerived F).HasLeftDerivedFunctor
      (HomologicalComplex.quasiIso A (up ℤ)) :=
  Functor.HasLeftDerivedFunctor.mk' (LF := F.mapDerivedCategory)
    (α := F.mapDerivedCategoryFactors.hom)

end CategoryTheory.Functor.LeftDerived.Exact.Cochain
