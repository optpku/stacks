module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import stacks_project.Chap92.Lemma_92_4_3
public import stacks_project.Chap92.Lemma_92_5_7_Kaehler
public import stacks_project.Chap92.«92_4_0_1_Morphism»
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived lower shriek of `O`, `underline{B}`, and `Ω_{O/A}` in `D(Ab)`

Lemma 92.5.7 records the identifications
`Lπ!(O) = Lπ!(underline{B}) = B` and
`L_{B/A} = Lπ!(Ω_{O/A} ⊗_O underline{B}) = Lπ!(Ω_{O/A})` in `D(Ab)`,
for `π`, `O`, and `underline{B}` as in 92.4.0.1.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Algebra
open Algebra.PolynomialSite
open Algebra.CotangentComplex
open CommAlgCat.Over.Polynomial
open Site
open scoped CategoryTheory

noncomputable section

universe u q q'

namespace CommAlgCat.Over.Polynomial
namespace Site

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

/-- The structure sheaf `O` on `C_{B/A}`, viewed as an abelian presheaf. -/
abbrev structureAbelianPresheaf : (PolynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (structureSheaf A B).obj ⋙
    forget₂ CommRingCat RingCat.{u} ⋙ forget₂ RingCat AddCommGrpCat.{u}

/-- Unfolding `structureAbelianPresheaf` recovers the double forgetful functor applied to `O`. -/
theorem structureAbelianPresheaf_eq :
    structureAbelianPresheaf A B =
      (structureSheaf A B).obj ⋙
        forget₂ CommRingCat RingCat.{u} ⋙ forget₂ RingCat AddCommGrpCat.{u} :=
  sorry

/-- The constant sheaf `underline{B}` on `C_{B/A}`, viewed as an abelian presheaf. -/
abbrev constantAbelianPresheaf : (PolynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (constantRingSheaf A B).obj ⋙
    forget₂ CommRingCat RingCat.{u} ⋙ forget₂ RingCat AddCommGrpCat.{u}

/-- Unfolding `constantAbelianPresheaf` recovers the double forgetful functor applied to
`underline{B}`. -/
theorem constantAbelianPresheaf_eq :
    constantAbelianPresheaf A B =
      (constantRingSheaf A B).obj ⋙
        forget₂ CommRingCat RingCat.{u} ⋙ forget₂ RingCat AddCommGrpCat.{u} :=
  sorry

end Site
end CommAlgCat.Over.Polynomial

namespace Algebra.PolynomialSite

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
variable [HasColimitsOfShape (PolynomialSite A B)ᵒᵖ AddCommGrpCat.{u}]
variable [HasDerivedCategory.{q'} AddCommGrpCat.{u}]
variable [HasDerivedCategory.{q} ((PolynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u})]
variable [Functor.HasLeftDerivedFunctor
  (categoryOverPointColimitToDerived (PolynomialSite A B) AddCommGrpCat.{u})
  (HomotopyCategory.quasiIso ((PolynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (ComplexShape.up ℤ))]

/-- Lemma 92.5.7 (1). Let `A → B` be a ring map, and let `π`, `O`, `underline{B}` be as in
92.4.0.1. Then `Lπ!(O) = B` in `D(Ab)`. -/
@[stacks 08QK]
theorem lowerShriek_structureSheaf :
    IsIsomorphic
      ((Lπ![(PolynomialSite A B), AddCommGrpCat.{u}]).obj
        ((DerivedCategory.singleFunctor
            ((PolynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u}) (0 : ℤ)).obj
          (structureAbelianPresheaf A B)))
      ((DerivedCategory.singleFunctor AddCommGrpCat.{u} (0 : ℤ)).obj
        (AddCommGrpCat.of B)) :=
  sorry

/-- Lemma 92.5.7 (2). Let `A → B` be a ring map, and let `π`, `O`, `underline{B}` be as in
92.4.0.1. Then `Lπ!(underline{B}) = B` in `D(Ab)`. -/
@[stacks 08QK]
theorem lowerShriek_constant :
    IsIsomorphic
      ((Lπ![(PolynomialSite A B), AddCommGrpCat.{u}]).obj
        ((DerivedCategory.singleFunctor
            ((PolynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u}) (0 : ℤ)).obj
          (constantAbelianPresheaf A B)))
      ((DerivedCategory.singleFunctor AddCommGrpCat.{u} (0 : ℤ)).obj
        (AddCommGrpCat.of B)) :=
  sorry

/-- Transitivity of the identifications `Lπ!(O) ≅ Lπ!(underline{B})` in `D(Ab)`. -/
theorem lowerShriek_structureSheaf_constant :
    IsIsomorphic
      ((Lπ![(PolynomialSite A B), AddCommGrpCat.{u}]).obj
        ((DerivedCategory.singleFunctor
            ((PolynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u}) (0 : ℤ)).obj
          (structureAbelianPresheaf A B)))
      ((Lπ![(PolynomialSite A B), AddCommGrpCat.{u}]).obj
        ((DerivedCategory.singleFunctor
            ((PolynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u}) (0 : ℤ)).obj
          (constantAbelianPresheaf A B))) :=
  sorry

end Algebra.PolynomialSite

namespace Algebra.CotangentComplex

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
variable [HasColimitsOfShape (PolynomialSite A B)ᵒᵖ AddCommGrpCat.{u}]
variable [HasDerivedCategory.{q'} AddCommGrpCat.{u}]
variable [HasDerivedCategory.{q} ((PolynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u})]
variable [Functor.HasLeftDerivedFunctor
  (categoryOverPointColimitToDerived (PolynomialSite A B) AddCommGrpCat.{u})
  (HomotopyCategory.quasiIso ((PolynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (ComplexShape.up ℤ))]
variable [HasColimitsOfShape (PolynomialSite A B)ᵒᵖ (ModuleCat.{u} B)]
variable [HasDerivedCategory.{q'} (ModuleCat.{u} B)]
variable [HasDerivedCategory.{q} ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B)]
variable [Functor.HasLeftDerivedFunctor
  (categoryOverPointColimitToDerived (PolynomialSite A B) (ModuleCat.{u} B))
  (HomotopyCategory.quasiIso ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B)
    (ComplexShape.up ℤ))]

/-- Lemma 92.5.7 (3). Let `A → B` be a ring map, and let `π`, `O`, `underline{B}` be as in
92.4.0.1. Then `L_{B/A} = Lπ!(Ω_{O/A} ⊗_O underline{B})` in `D(Ab)`, obtained by applying
the derived forgetful functor `D(B) ⥤ D(Ab)` to the identification of Lemma 92.4.3. -/
@[stacks 08QK]
theorem forgetDerived_lowerShriek_omega :
    IsIsomorphic
      ((forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}).mapDerivedCategory.obj
        (DerivedCategory.Q.obj (Algebra.cotangentComplex A B)))
      ((forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}).mapDerivedCategory.obj
        ((Lπ![(PolynomialSite A B), (ModuleCat.{u} B)]).obj
          ((DerivedCategory.singleFunctor
              ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B) (0 : ℤ)).obj
            (omegaSheaf A B)))) :=
  sorry

/-- Lemma 92.5.7 (4). Let `A → B` be a ring map, and let `π`, `O`, `underline{B}` be as in
92.4.0.1. Then `Lπ!(Ω_{O/A} ⊗_O underline{B}) = Lπ!(Ω_{O/A})` in `D(Ab)`. -/
@[stacks 08QK]
theorem lowerShriek_omega_kaehler :
    IsIsomorphic
      ((forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}).mapDerivedCategory.obj
        ((Lπ![(PolynomialSite A B), (ModuleCat.{u} B)]).obj
          ((DerivedCategory.singleFunctor
              ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B) (0 : ℤ)).obj
            (omegaSheaf A B))))
      ((Lπ![(PolynomialSite A B), AddCommGrpCat.{u}]).obj
        ((DerivedCategory.singleFunctor
            ((PolynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u}) (0 : ℤ)).obj
          (kaehlerPresheaf A B))) :=
  sorry

end Algebra.CotangentComplex
