/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus

/-!
# Homology of the total right derived functor on injective complexes
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open DerivedCategory.Plus (Qh homologyFunctor)

noncomputable section

universe wA wB vA vB uA uB

namespace CategoryTheory.Functor.RightDerived
namespace Bounded

variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable {B : Type uB} [Category.{vB} B] [Abelian B]
variable [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
variable (F : A ⥤ B) [F.Additive] [EnoughInjectives A]

/-- Homology of the image of a termwise-injective bounded-below complex is canonically
isomorphic to homology after applying the total right derived functor. -/
noncomputable def injectiveHomologyIso
    (K : CochainComplex.Plus A) [∀ n : ℤ, Injective (K.obj.X n)] (i : ℤ) :
    ((CochainComplex.Plus.ι B).obj (F.mapCochainComplexPlus.obj K)).homology i ≅
      (homologyFunctor B i).obj
        (F.rightDerivedFunctorPlus.obj (Qh.obj ((HomotopyCategory.Plus.quotient A).obj K))) :=
  (HomotopyCategory.homologyFunctorFactors B (ComplexShape.up ℤ) i).symm.app
      (F.mapCochainComplexPlus.obj K).obj ≪≫
    (HomotopyCategory.homologyFunctor B (ComplexShape.up ℤ) i).mapIso
      ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).symm.app K.obj) ≪≫
    (DerivedCategory.homologyFunctorFactorsh B i).symm.app
      (F.mapHomotopyCategoryPlus.obj ((HomotopyCategory.Plus.quotient A).obj K)).obj ≪≫
    (homologyFunctor B i).mapIso
      (asIso (F.rightDerivedFunctorPlusUnit.app
        ((HomotopyCategory.Plus.quotient A).obj K)) :
        (F.mapHomotopyCategoryPlus ⋙ Qh).obj
            ((HomotopyCategory.Plus.quotient A).obj K) ≅
          (Qh ⋙ F.rightDerivedFunctorPlus).obj
            ((HomotopyCategory.Plus.quotient A).obj K))

/-- The injective-complex homology comparison is natural in cochain maps. -/
@[reassoc]
theorem injectiveHomologyIso_hom_naturality
    {K L : CochainComplex.Plus A}
    [∀ n : ℤ, Injective (K.obj.X n)] [∀ n : ℤ, Injective (L.obj.X n)]
    (f : K ⟶ L) (i : ℤ) :
    (F.mapCochainComplexPlus ⋙ CochainComplex.Plus.ι B ⋙
          HomologicalComplex.homologyFunctor B (ComplexShape.up ℤ) i).map f ≫
        (injectiveHomologyIso F L i).hom =
      (injectiveHomologyIso F K i).hom ≫
        (HomotopyCategory.Plus.quotient A ⋙ Qh ⋙
          F.rightDerivedFunctorPlus ⋙ homologyFunctor B i).map f := sorry

end Bounded
end RightDerived
end Functor
end CategoryTheory
