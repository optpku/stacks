module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Colimit.InverseImage
public import stacks_project.Chap92.Lemma_92_4_1_PolynomialOver
public import stacks_project.Chap92.«92_7_0_2»
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived and underived lower shriek when the top algebra is polynomial

Lemma 92.7.2 identifies `Lπ_!(g3⁻¹ F)`, `Lπ_{3,!} F`, and `π_{3,!} F` in `D(Ab)`
for abelian sheaves on `C_{C/B}` when `C` is a polynomial `B`-algebra, using the
three maps of (92.7.0.2).
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Algebra
open RingedSite.Cotangent.PolynomialTriple
open scoped CategoryTheory

universe u q q' t

namespace RingedSite.Cotangent.PolynomialTriple

variable (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
variable [IsPolynomial B C]
include A

variable [HasColimitsOfShape (PolynomialSite B C)ᵒᵖ AddCommGrpCat.{u}]
variable [HasColimitsOfShape (site A B C)ᵒᵖ AddCommGrpCat.{u}]
variable [HasDerivedCategory.{t} AddCommGrpCat.{u}]
variable [HasDerivedCategory.{q} ((PolynomialSite B C)ᵒᵖ ⥤ AddCommGrpCat.{u})]
variable [HasDerivedCategory.{q'} ((site A B C)ᵒᵖ ⥤ AddCommGrpCat.{u})]
variable [Functor.HasLeftDerivedFunctor
  (categoryOverPointColimitToDerived (PolynomialSite B C) AddCommGrpCat.{u})
  (HomotopyCategory.quasiIso ((PolynomialSite B C)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (ComplexShape.up ℤ))]
variable [Functor.HasLeftDerivedFunctor
  (categoryOverPointColimitToDerived (site A B C) AddCommGrpCat.{u})
  (HomotopyCategory.quasiIso ((site A B C)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (ComplexShape.up ℤ))]

/-- Lemma 92.7.2 (1). With notation as in (92.7.0.2), if `C` is a polynomial
`B`-algebra then for every abelian sheaf `F` on `C_{C/B}` one has
`Lπ_!(g3⁻¹ F) = Lπ_{3,!} F` in `D(Ab)`. Here `g3⁻¹` is inverse image along
`u3`, `Lπ_!` is `Lπ![site A B C, AddCommGrpCat]`, and `Lπ_{3,!}` is
`Lπ![PolynomialSite B C, AddCommGrpCat]`, compared on the heart. -/
@[stacks 08QV]
theorem lowerShriek_u3InverseImage :
    IsIsomorphic
      ((DerivedCategory.singleFunctor
          ((PolynomialSite B C)ᵒᵖ ⥤ AddCommGrpCat.{u}) (0 : ℤ)) ⋙
        (Functor.presheafInverseImage (u3 A B C) AddCommGrpCat.{u}).mapDerivedCategory ⋙
        Lπ![(site A B C), AddCommGrpCat.{u}])
      ((DerivedCategory.singleFunctor
          ((PolynomialSite B C)ᵒᵖ ⥤ AddCommGrpCat.{u}) (0 : ℤ)) ⋙
        Lπ![(PolynomialSite B C), AddCommGrpCat.{u}]) :=
  sorry

/-- Objectwise form of `Lπ_!(g3⁻¹ F) = Lπ_{3,!} F` in `D(Ab)`. -/
theorem lowerShriek_u3InverseImage_obj
    (F : (PolynomialSite B C)ᵒᵖ ⥤ AddCommGrpCat.{u}) :
    IsIsomorphic
      (((DerivedCategory.singleFunctor
          ((PolynomialSite B C)ᵒᵖ ⥤ AddCommGrpCat.{u}) (0 : ℤ)) ⋙
        (Functor.presheafInverseImage (u3 A B C) AddCommGrpCat.{u}).mapDerivedCategory ⋙
        Lπ![(site A B C), AddCommGrpCat.{u}]).obj F)
      (((DerivedCategory.singleFunctor
          ((PolynomialSite B C)ᵒᵖ ⥤ AddCommGrpCat.{u}) (0 : ℤ)) ⋙
        Lπ![(PolynomialSite B C), AddCommGrpCat.{u}]).obj F) :=
  sorry

/-- Lemma 92.7.2 (2). With notation as in (92.7.0.2), if `C` is a polynomial
`B`-algebra then for every abelian sheaf `F` on `C_{C/B}` one has
`Lπ_{3,!} F = π_{3,!} F` in `D(Ab)`. Here `Lπ_{3,!}` is
`Lπ![PolynomialSite B C, AddCommGrpCat]` and underived `π_{3,!}` is `colim`,
compared on the heart; exactness of `colim` is Lemma 92.4.6. -/
@[stacks 08QV]
theorem lowerShriek_eq_underived :
    IsIsomorphic
      ((DerivedCategory.singleFunctor
          ((PolynomialSite B C)ᵒᵖ ⥤ AddCommGrpCat.{u}) (0 : ℤ)) ⋙
        Lπ![(PolynomialSite B C), AddCommGrpCat.{u}])
      (colim ⋙ DerivedCategory.singleFunctor AddCommGrpCat.{u} (0 : ℤ)) :=
  sorry

/-- Objectwise form of `Lπ_{3,!} F = π_{3,!} F` in `D(Ab)`. -/
theorem lowerShriek_eq_underived_obj
    (F : (PolynomialSite B C)ᵒᵖ ⥤ AddCommGrpCat.{u}) :
    IsIsomorphic
      ((Lπ![(PolynomialSite B C), AddCommGrpCat.{u}]).obj
        ((DerivedCategory.singleFunctor
            ((PolynomialSite B C)ᵒᵖ ⥤ AddCommGrpCat.{u}) (0 : ℤ)).obj F))
      ((DerivedCategory.singleFunctor AddCommGrpCat.{u} (0 : ℤ)).obj (colim.obj F)) :=
  sorry

/-- Composite identification `Lπ_!(u3⁻¹ F) ≅ (colim F)[0]` in `D(Ab)`. -/
theorem lowerShriek_u3InverseImage_eq_underived
    (F : (PolynomialSite B C)ᵒᵖ ⥤ AddCommGrpCat.{u}) :
    IsIsomorphic
      ((Lπ![(site A B C), AddCommGrpCat.{u}]).obj
        ((Functor.presheafInverseImage (u3 A B C) AddCommGrpCat.{u}).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor
              ((PolynomialSite B C)ᵒᵖ ⥤ AddCommGrpCat.{u}) (0 : ℤ)).obj F)))
      ((DerivedCategory.singleFunctor AddCommGrpCat.{u} (0 : ℤ)).obj (colim.obj F)) :=
  sorry

end RingedSite.Cotangent.PolynomialTriple
