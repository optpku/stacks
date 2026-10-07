module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Colimit.Connected
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Colimit.InverseImage
public import stacks_project.Chap92.Lemma_92_4_1_PolynomialOver
public import stacks_project.Chap92.«92_7_0_2»
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived lower shriek after inverse image along the three triangle maps

Lemma 92.7.3 records `Lg_{i,!} ∘ g_i⁻¹ = id` on `D(Ab)` of the target site and the
comparison `Lπ_! ∘ g_i⁻¹ = Lπ_{i,!}` for the three maps of (92.7.0.2), with no extra
polynomial hypothesis on `C/B`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Algebra
open RingedSite.Cotangent.PolynomialTriple
open scoped CategoryTheory

noncomputable section

universe u uC uC' v v' q q' q1 q2 q3 t

namespace RingedSite.Cotangent.PolynomialTriple

section PresheafLowerShriek

variable {C : Type uC} [Category.{v} C]
variable {C' : Type uC'} [Category.{v'} C']
variable (u : C' ⥤ C)
variable [∀ F : C'ᵒᵖ ⥤ AddCommGrpCat.{u}, u.op.HasLeftKanExtension F]

/-- Left Kan extension along `u.op` is additive on abelian-group-valued presheaves. -/
instance presheafLan_additive :
    (u.op.lan :
        (C'ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ (Cᵒᵖ ⥤ AddCommGrpCat.{u})).Additive :=
  sorry

variable [HasDerivedCategory.{q} (Cᵒᵖ ⥤ AddCommGrpCat.{u})]
variable [HasDerivedCategory.{q'} (C'ᵒᵖ ⥤ AddCommGrpCat.{u})]
variable [Functor.HasLeftDerivedFunctor
  (Functor.Homotopy.toDerived
    (u.op.lan : (C'ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ (Cᵒᵖ ⥤ AddCommGrpCat.{u})))
  (HomotopyCategory.quasiIso (C'ᵒᵖ ⥤ AddCommGrpCat.{u}) (ComplexShape.up ℤ))]

/-- The total left derived functor of presheaf lower shriek `u.op.lan`, i.e. `Lg_!`
for inverse image along `u`. -/
noncomputable abbrev derivedPresheafLowerShriek :
    DerivedCategory (C'ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤
      DerivedCategory (Cᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  (Functor.Homotopy.toDerived
      (u.op.lan : (C'ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ (Cᵒᵖ ⥤ AddCommGrpCat.{u}))).totalLeftDerived
    (DerivedCategory.Qh :
      HomotopyCategory (C'ᵒᵖ ⥤ AddCommGrpCat.{u}) (ComplexShape.up ℤ) ⥤
        DerivedCategory (C'ᵒᵖ ⥤ AddCommGrpCat.{u}))
    (HomotopyCategory.quasiIso (C'ᵒᵖ ⥤ AddCommGrpCat.{u}) (ComplexShape.up ℤ))

/-- Unfolding of derived presheaf lower shriek as a total left derived functor. -/
theorem derivedPresheafLowerShriek_eq :
    derivedPresheafLowerShriek u =
      (Functor.Homotopy.toDerived
          (u.op.lan : (C'ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ (Cᵒᵖ ⥤ AddCommGrpCat.{u}))).totalLeftDerived
        (DerivedCategory.Qh :
          HomotopyCategory (C'ᵒᵖ ⥤ AddCommGrpCat.{u}) (ComplexShape.up ℤ) ⥤
            DerivedCategory (C'ᵒᵖ ⥤ AddCommGrpCat.{u}))
        (HomotopyCategory.quasiIso (C'ᵒᵖ ⥤ AddCommGrpCat.{u}) (ComplexShape.up ℤ)) :=
  sorry

/-- The derived inverse-image/lower-shriek composite carries the right-derived
structure needed for its canonical counit. -/
noncomputable instance lowerShriekInverseImage_comp_isRightDerivedFunctor :
    Functor.IsRightDerivedFunctor
      ((Functor.presheafInverseImage u AddCommGrpCat.{u}).mapDerivedCategory ⋙
        derivedPresheafLowerShriek u)
      (Functor.whiskerRight
          ((Functor.presheafInverseImage u AddCommGrpCat.{u}).mapDerivedCategoryFactorsh.inv)
          (derivedPresheafLowerShriek u) ≫
        (Functor.associator
          (DerivedCategory.Qh :
            HomotopyCategory (Cᵒᵖ ⥤ AddCommGrpCat.{u}) (ComplexShape.up ℤ) ⥤
              DerivedCategory (Cᵒᵖ ⥤ AddCommGrpCat.{u}))
          (Functor.presheafInverseImage u AddCommGrpCat.{u}).mapDerivedCategory
          (derivedPresheafLowerShriek u)).hom)
      (HomotopyCategory.quasiIso (Cᵒᵖ ⥤ AddCommGrpCat.{u}) (ComplexShape.up ℤ)) :=
  sorry

/-- The canonical derived counit `g⁻¹ ⋙ Lg_! ⟶ 𝟭` of `lan ⊣ presheafInverseImage`. -/
noncomputable def lowerShriekInverseImageCounit :
    (Functor.presheafInverseImage u AddCommGrpCat.{u}).mapDerivedCategory ⋙
        derivedPresheafLowerShriek u ⟶
      𝟭 (DerivedCategory (Cᵒᵖ ⥤ AddCommGrpCat.{u})) :=
  Adjunction.derivedε
    (Adjunction.mapHomotopyCategoryAdjunction
      (u.op.lanAdjunction AddCommGrpCat.{u}))
    (HomotopyCategory.quasiIso (Cᵒᵖ ⥤ AddCommGrpCat.{u}) (ComplexShape.up ℤ))
    ((Functor.Homotopy.toDerived
        (u.op.lan : (C'ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ (Cᵒᵖ ⥤ AddCommGrpCat.{u}))).totalLeftDerivedCounit
      (DerivedCategory.Qh :
        HomotopyCategory (C'ᵒᵖ ⥤ AddCommGrpCat.{u}) (ComplexShape.up ℤ) ⥤
          DerivedCategory (C'ᵒᵖ ⥤ AddCommGrpCat.{u}))
      (HomotopyCategory.quasiIso (C'ᵒᵖ ⥤ AddCommGrpCat.{u}) (ComplexShape.up ℤ)))
    ((Functor.presheafInverseImage u AddCommGrpCat.{u}).mapDerivedCategoryFactorsh.inv)

/-- The derived counit is the derived adjunction counit of `u.op.lanAdjunction`. -/
theorem lowerShriekInverseImageCounit_eq :
    lowerShriekInverseImageCounit u =
      Adjunction.derivedε
        (Adjunction.mapHomotopyCategoryAdjunction
          (u.op.lanAdjunction AddCommGrpCat.{u}))
        (HomotopyCategory.quasiIso (Cᵒᵖ ⥤ AddCommGrpCat.{u}) (ComplexShape.up ℤ))
        ((Functor.Homotopy.toDerived
            (u.op.lan :
              (C'ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ (Cᵒᵖ ⥤ AddCommGrpCat.{u}))).totalLeftDerivedCounit
          (DerivedCategory.Qh :
            HomotopyCategory (C'ᵒᵖ ⥤ AddCommGrpCat.{u}) (ComplexShape.up ℤ) ⥤
              DerivedCategory (C'ᵒᵖ ⥤ AddCommGrpCat.{u}))
          (HomotopyCategory.quasiIso (C'ᵒᵖ ⥤ AddCommGrpCat.{u}) (ComplexShape.up ℤ)))
        ((Functor.presheafInverseImage u AddCommGrpCat.{u}).mapDerivedCategoryFactorsh.inv) :=
  sorry

end PresheafLowerShriek

variable (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]

variable [HasColimitsOfShape (site A B C)ᵒᵖ AddCommGrpCat.{u}]
variable [HasColimitsOfShape (PolynomialSite A B)ᵒᵖ AddCommGrpCat.{u}]
variable [HasColimitsOfShape (PolynomialSite A C)ᵒᵖ AddCommGrpCat.{u}]
variable [HasColimitsOfShape (PolynomialSite B C)ᵒᵖ AddCommGrpCat.{u}]
variable [HasDerivedCategory.{t} AddCommGrpCat.{u}]
variable [HasDerivedCategory.{q} ((site A B C)ᵒᵖ ⥤ AddCommGrpCat.{u})]
variable [HasDerivedCategory.{q1} ((PolynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u})]
variable [HasDerivedCategory.{q2} ((PolynomialSite A C)ᵒᵖ ⥤ AddCommGrpCat.{u})]
variable [HasDerivedCategory.{q3} ((PolynomialSite B C)ᵒᵖ ⥤ AddCommGrpCat.{u})]
variable [Functor.HasLeftDerivedFunctor
  (categoryOverPointColimitToDerived (site A B C) AddCommGrpCat.{u})
  (HomotopyCategory.quasiIso ((site A B C)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (ComplexShape.up ℤ))]
variable [Functor.HasLeftDerivedFunctor
  (categoryOverPointColimitToDerived (PolynomialSite A B) AddCommGrpCat.{u})
  (HomotopyCategory.quasiIso ((PolynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (ComplexShape.up ℤ))]
variable [Functor.HasLeftDerivedFunctor
  (categoryOverPointColimitToDerived (PolynomialSite A C) AddCommGrpCat.{u})
  (HomotopyCategory.quasiIso ((PolynomialSite A C)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (ComplexShape.up ℤ))]
variable [Functor.HasLeftDerivedFunctor
  (categoryOverPointColimitToDerived (PolynomialSite B C) AddCommGrpCat.{u})
  (HomotopyCategory.quasiIso ((PolynomialSite B C)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (ComplexShape.up ℤ))]
variable [∀ F : (site A B C)ᵒᵖ ⥤ AddCommGrpCat.{u},
  (u1 A B C).op.HasLeftKanExtension F]
variable [∀ F : (site A B C)ᵒᵖ ⥤ AddCommGrpCat.{u},
  (u2 A B C).op.HasLeftKanExtension F]
variable [∀ F : (site A B C)ᵒᵖ ⥤ AddCommGrpCat.{u},
  (u3 A B C).op.HasLeftKanExtension F]
variable [Functor.HasLeftDerivedFunctor
  (Functor.Homotopy.toDerived
    ((u1 A B C).op.lan :
      ((site A B C)ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤
        ((PolynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u})))
  (HomotopyCategory.quasiIso ((site A B C)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (ComplexShape.up ℤ))]
variable [Functor.HasLeftDerivedFunctor
  (Functor.Homotopy.toDerived
    ((u2 A B C).op.lan :
      ((site A B C)ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤
        ((PolynomialSite A C)ᵒᵖ ⥤ AddCommGrpCat.{u})))
  (HomotopyCategory.quasiIso ((site A B C)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (ComplexShape.up ℤ))]
variable [Functor.HasLeftDerivedFunctor
  (Functor.Homotopy.toDerived
    ((u3 A B C).op.lan :
      ((site A B C)ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤
        ((PolynomialSite B C)ᵒᵖ ⥤ AddCommGrpCat.{u})))
  (HomotopyCategory.quasiIso ((site A B C)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (ComplexShape.up ℤ))]

/-- Lemma 92.7.3 (1). With notation as in (92.7.0.2), `Lg_{1,!} ∘ g1⁻¹ = id` on
`D(Ab)` of `C_{B/A}`. Here `g1⁻¹` is inverse image along `u1` and `Lg_{1,!}` is
the total left derived functor of `u1.op.lan`. -/
@[stacks 08QW]
instance u1_lowerShriek_inverseImage_isIso :
    IsIso (lowerShriekInverseImageCounit (u1 A B C)) :=
  sorry

/-- Objectwise form of `Lg_{1,!} (g1⁻¹ F) ≅ F` on the heart of `D(Ab)` of `C_{B/A}`. -/
theorem u1_lowerShriek_inverseImage_obj
    (F : (PolynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u}) :
    IsIsomorphic
      ((derivedPresheafLowerShriek (u1 A B C)).obj
        ((Functor.presheafInverseImage (u1 A B C) AddCommGrpCat.{u}).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor
              ((PolynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u}) (0 : ℤ)).obj F)))
      ((DerivedCategory.singleFunctor
          ((PolynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u}) (0 : ℤ)).obj F) :=
  sorry

/-- Lemma 92.7.3 (2). With notation as in (92.7.0.2), `Lg_{2,!} ∘ g2⁻¹ = id` on
`D(Ab)` of `C_{C/A}`. Here `g2⁻¹` is inverse image along `u2` and `Lg_{2,!}` is
the total left derived functor of `u2.op.lan`. -/
@[stacks 08QW]
instance u2_lowerShriek_inverseImage_isIso :
    IsIso (lowerShriekInverseImageCounit (u2 A B C)) :=
  sorry

/-- Objectwise form of `Lg_{2,!} (g2⁻¹ F) ≅ F` on the heart of `D(Ab)` of `C_{C/A}`. -/
theorem u2_lowerShriek_inverseImage_obj
    (F : (PolynomialSite A C)ᵒᵖ ⥤ AddCommGrpCat.{u}) :
    IsIsomorphic
      ((derivedPresheafLowerShriek (u2 A B C)).obj
        ((Functor.presheafInverseImage (u2 A B C) AddCommGrpCat.{u}).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor
              ((PolynomialSite A C)ᵒᵖ ⥤ AddCommGrpCat.{u}) (0 : ℤ)).obj F)))
      ((DerivedCategory.singleFunctor
          ((PolynomialSite A C)ᵒᵖ ⥤ AddCommGrpCat.{u}) (0 : ℤ)).obj F) :=
  sorry

/-- Lemma 92.7.3 (3). With notation as in (92.7.0.2), `Lg_{3,!} ∘ g3⁻¹ = id` on
`D(Ab)` of `C_{C/B}`. Here `g3⁻¹` is inverse image along `u3` and `Lg_{3,!}` is
the total left derived functor of `u3.op.lan`. -/
@[stacks 08QW]
instance u3_lowerShriek_inverseImage_isIso :
    IsIso (lowerShriekInverseImageCounit (u3 A B C)) :=
  sorry

/-- Objectwise form of `Lg_{3,!} (g3⁻¹ F) ≅ F` on the heart of `D(Ab)` of `C_{C/B}`. -/
theorem u3_lowerShriek_inverseImage_obj
    (F : (PolynomialSite B C)ᵒᵖ ⥤ AddCommGrpCat.{u}) :
    IsIsomorphic
      ((derivedPresheafLowerShriek (u3 A B C)).obj
        ((Functor.presheafInverseImage (u3 A B C) AddCommGrpCat.{u}).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor
              ((PolynomialSite B C)ᵒᵖ ⥤ AddCommGrpCat.{u}) (0 : ℤ)).obj F)))
      ((DerivedCategory.singleFunctor
          ((PolynomialSite B C)ᵒᵖ ⥤ AddCommGrpCat.{u}) (0 : ℤ)).obj F) :=
  sorry

/-- Lemma 92.7.3 (4). With notation as in (92.7.0.2), `Lπ_! ∘ g1⁻¹ = Lπ_{1,!}` as
functors `D(Ab on C_{B/A}) → D(Ab)`. Here `g1⁻¹` is inverse image along `u1`,
`Lπ_!` is `Lπ![site A B C, AddCommGrpCat]`, and `Lπ_{1,!}` is
`Lπ![PolynomialSite A B, AddCommGrpCat]`. -/
@[stacks 08QW]
instance u1_inverseImageComparison_isIso :
    IsIso (DerivedColimit.inverseImageComparison AddCommGrpCat.{u} (u1 A B C)) :=
  sorry

/-- Objectwise form of `Lπ_! (g1⁻¹ F) ≅ Lπ_{1,!} F` on the heart. -/
theorem u1_inverseImageComparison_obj
    (F : (PolynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u}) :
    IsIsomorphic
      ((Lπ![(site A B C), AddCommGrpCat.{u}]).obj
        ((Functor.presheafInverseImage (u1 A B C) AddCommGrpCat.{u}).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor
              ((PolynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u}) (0 : ℤ)).obj F)))
      ((Lπ![(PolynomialSite A B), AddCommGrpCat.{u}]).obj
        ((DerivedCategory.singleFunctor
            ((PolynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u}) (0 : ℤ)).obj F)) :=
  sorry

/-- Lemma 92.7.3 (5). With notation as in (92.7.0.2), `Lπ_! ∘ g2⁻¹ = Lπ_{2,!}` as
functors `D(Ab on C_{C/A}) → D(Ab)`. Here `g2⁻¹` is inverse image along `u2`,
`Lπ_!` is `Lπ![site A B C, AddCommGrpCat]`, and `Lπ_{2,!}` is
`Lπ![PolynomialSite A C, AddCommGrpCat]`. -/
@[stacks 08QW]
instance u2_inverseImageComparison_isIso :
    IsIso (DerivedColimit.inverseImageComparison AddCommGrpCat.{u} (u2 A B C)) :=
  sorry

/-- Objectwise form of `Lπ_! (g2⁻¹ F) ≅ Lπ_{2,!} F` on the heart. -/
theorem u2_inverseImageComparison_obj
    (F : (PolynomialSite A C)ᵒᵖ ⥤ AddCommGrpCat.{u}) :
    IsIsomorphic
      ((Lπ![(site A B C), AddCommGrpCat.{u}]).obj
        ((Functor.presheafInverseImage (u2 A B C) AddCommGrpCat.{u}).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor
              ((PolynomialSite A C)ᵒᵖ ⥤ AddCommGrpCat.{u}) (0 : ℤ)).obj F)))
      ((Lπ![(PolynomialSite A C), AddCommGrpCat.{u}]).obj
        ((DerivedCategory.singleFunctor
            ((PolynomialSite A C)ᵒᵖ ⥤ AddCommGrpCat.{u}) (0 : ℤ)).obj F)) :=
  sorry

/-- Lemma 92.7.3 (6). With notation as in (92.7.0.2), `Lπ_! ∘ g3⁻¹ = Lπ_{3,!}` as
functors `D(Ab on C_{C/B}) → D(Ab)`. Here `g3⁻¹` is inverse image along `u3`,
`Lπ_!` is `Lπ![site A B C, AddCommGrpCat]`, and `Lπ_{3,!}` is
`Lπ![PolynomialSite B C, AddCommGrpCat]`. -/
@[stacks 08QW]
instance u3_inverseImageComparison_isIso :
    IsIso (DerivedColimit.inverseImageComparison AddCommGrpCat.{u} (u3 A B C)) :=
  sorry

/-- Objectwise form of `Lπ_! (g3⁻¹ F) ≅ Lπ_{3,!} F` on the heart. -/
theorem u3_inverseImageComparison_obj
    (F : (PolynomialSite B C)ᵒᵖ ⥤ AddCommGrpCat.{u}) :
    IsIsomorphic
      ((Lπ![(site A B C), AddCommGrpCat.{u}]).obj
        ((Functor.presheafInverseImage (u3 A B C) AddCommGrpCat.{u}).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor
              ((PolynomialSite B C)ᵒᵖ ⥤ AddCommGrpCat.{u}) (0 : ℤ)).obj F)))
      ((Lπ![(PolynomialSite B C), AddCommGrpCat.{u}]).obj
        ((DerivedCategory.singleFunctor
            ((PolynomialSite B C)ᵒᵖ ⥤ AddCommGrpCat.{u}) (0 : ℤ)).obj F)) :=
  sorry

end RingedSite.Cotangent.PolynomialTriple

