module

public import ReasLib.Algebra.PolynomialSite.Constant
import StacksCheckRecall

/-!
# Derived lower shriek of a constant module on the polynomial site

Lemma 92.4.4 identifies `Lπ!(π⁻¹ M)` with `M` in `D(B)` for the morphism of ringed topoi
`π` of 92.4.0.1, via invertibility of the derived constant/colimit counit on `PolynomialSite A B`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Algebra
open Algebra.PolynomialSite
open CategoryTheory.DerivedColimit
open scoped CategoryTheory

universe u q q'

namespace Algebra.PolynomialSite

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable [HasColimitsOfShape (PolynomialSite A B)ᵒᵖ (ModuleCat.{u} B)]
variable [HasDerivedCategory.{q'} (ModuleCat.{u} B)]
variable [HasDerivedCategory.{q} ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B)]
variable [Functor.HasLeftDerivedFunctor
  (categoryOverPointColimitToDerived (PolynomialSite A B) (ModuleCat.{u} B))
  (HomotopyCategory.quasiIso ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B)
    (ComplexShape.up ℤ))]

/- Lemma 92.4.4. If `A → B` is a ring map, then `Lπ!(π⁻¹ M) = M` in `D(B)`, with `π` as in
92.4.0.1, recorded here as invertibility of the derived counit of `Lπ!` on `PolynomialSite A B`
with coefficients in `ModuleCat B`. -/
@[stacks 08QE]
#check (Algebra.PolynomialSite.lowerShriek_inverseImage_isIso :
    IsIso
      (derivedColimitCounit :
        (derivedConstant :
            DerivedCategory.{q'} (ModuleCat.{u} B) ⥤
              DerivedCategory.{q} ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B)) ⋙
          Lπ![(PolynomialSite A B), (ModuleCat.{u} B)] ⟶
            𝟭 (DerivedCategory.{q'} (ModuleCat.{u} B))))

/- Objectwise form of the derived counit: `Lπ!(π⁻¹ M) ≅ M` in `D(B)`. -/
#check (Algebra.PolynomialSite.lowerShriek_inverseImage_obj :
    ∀ (M : DerivedCategory.{q'} (ModuleCat.{u} B)),
    IsIsomorphic
      ((Lπ![(PolynomialSite A B), (ModuleCat.{u} B)]).obj
        ((derivedConstant :
            DerivedCategory.{q'} (ModuleCat.{u} B) ⥤
              DerivedCategory.{q} ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B)).obj M))
      M)

/- Source-facing underived form: `Lπ!(π⁻¹ (M[0])) ≅ M[0]` for `M : ModuleCat B`. -/
#check (Algebra.PolynomialSite.lowerShriek_inverseImage_single :
    ∀ (M : ModuleCat.{u} B),
    IsIsomorphic
      ((Lπ![(PolynomialSite A B), (ModuleCat.{u} B)]).obj
        ((derivedConstant :
            DerivedCategory.{q'} (ModuleCat.{u} B) ⥤
              DerivedCategory.{q} ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B)).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} B) (0 : ℤ)).obj M)))
      ((DerivedCategory.singleFunctor (ModuleCat.{u} B) (0 : ℤ)).obj M))

end Algebra.PolynomialSite
