module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Cochain
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Homotopy.Naturality
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact
public import ReasLib.CategoryTheory.Functor.Derived.Composition.Right
public import ReasLib.CategoryTheory.Functor.Derived.Exact.Cochain
public import ReasLib.CategoryTheory.Functor.Exactness.Additive
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.Tactic.CrossRefAttribute

/-!
# Total right derivation after an exact functor

This leaf compares the total right-derived functor of `F.obj ⋙ G` with the composite of the
derived functor of an exact `F` and the total right-derived functor of `G`. The comparison is an
isomorphism when `F.obj` preserves injective objects.
-/

@[expose] public section

open CategoryTheory Limits ComplexShape

noncomputable section

universe uA vA wA uB vB wB uC vC wC

namespace CategoryTheory.Functor.RightDerived.Cochain.ExactFirst

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
variable {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]

/-- The cochain-level localization of a composite agrees with first applying the exact functor
on complexes and then applying the cochain-level localization of the second functor. -/
@[stacks 05T2 "cochain comparison for an exact first functor"]
noncomputable def toIteratedIso
    (F : A ⥤ₑ B) (G : B ⥤ C) [G.Additive] :
    RightDerived.Cochain.toDerived (F.obj ⋙ G) ≅
      F.obj.mapHomologicalComplex (up ℤ) ⋙ RightDerived.Cochain.toDerived G :=
  Functor.isoWhiskerRight
      (Functor.mapHomologicalComplexCompIso (Iso.refl (F.obj ⋙ G)) (up ℤ)).symm
      (DerivedCategory.Q : CochainComplex C ℤ ⥤ DerivedCategory C) ≪≫
    Functor.associator _ _ _

/-- The right-derived unit obtained by first deriving an exact functor and then deriving the
second functor. -/
@[stacks 05T2 "iterated unit for an exact first functor"]
noncomputable def unit
    (F : A ⥤ₑ B) (G : B ⥤ C) [G.Additive]
    [(RightDerived.Cochain.toDerived G).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso B (up ℤ))] :
    RightDerived.Cochain.toDerived (F.obj ⋙ G) ⟶
      (DerivedCategory.Q : CochainComplex A ℤ ⥤ DerivedCategory A) ⋙
        (F.mapDerivedCategory ⋙ RightDerived.Cochain.functor G) :=
  (toIteratedIso F G).hom ≫
    RightDerived.Composition.iteratedUnit
      F.obj.mapDerivedCategoryFactors.inv (RightDerived.Cochain.unit G)

/-- If the exact first functor preserves injectives, its iterated model is a right-derived
functor of the underived composite. -/
@[stacks 05T2 "exact-first iterated right-derived model"]
noncomputable instance isRightDerived
    (F : A ⥤ₑ B) (G : B ⥤ C) [G.Additive] [F.obj.PreservesInjectiveObjects]
    [(RightDerived.Cochain.toDerived G).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso B (up ℤ))] :
    (F.mapDerivedCategory ⋙ RightDerived.Cochain.functor G).IsRightDerivedFunctor
      (unit F G) (HomologicalComplex.quasiIso A (up ℤ)) := sorry

/-- Total right derivation commutes with precomposition by an exact functor which preserves
injective objects. Both maps are the canonical right-derived uniqueness transformations. -/
@[stacks 05T2 "total right derivation after an exact functor"]
noncomputable def iso
    (F : A ⥤ₑ B) (G : B ⥤ C) [G.Additive] [F.obj.PreservesInjectiveObjects]
    [(RightDerived.Cochain.toDerived G).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso B (up ℤ))]
    [(RightDerived.Cochain.toDerived (F.obj ⋙ G)).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso A (up ℤ))] :
    F.mapDerivedCategory ⋙ RightDerived.Cochain.functor G ≅
      RightDerived.Cochain.functor (F.obj ⋙ G) :=
  RightDerived.natIsoOfIso
    (DerivedCategory.Q : CochainComplex A ℤ ⥤ DerivedCategory A)
    (HomologicalComplex.quasiIso A (up ℤ))
    (unit F G) (RightDerived.Cochain.unit (F.obj ⋙ G)) (Iso.refl _)

/- The only deferred fact is the proposition that the iterated model has the universal
right-derived property. The comparison functors, units, and both maps of `iso` are explicit. -/

end CategoryTheory.Functor.RightDerived.Cochain.ExactFirst
