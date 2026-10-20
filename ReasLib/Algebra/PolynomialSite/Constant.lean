module

public import ReasLib.Algebra.PolynomialSite
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Colimit.Connected
public import Mathlib.CategoryTheory.IsomorphismClasses

/-!
# Derived lower shriek of constant modules on the polynomial site

For any commutative ring map, the canonical derived constant-colimit counit on the
polynomial site is invertible.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.DerivedColimit
open scoped CategoryTheory

universe u q q'

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable [HasColimitsOfShape (Algebra.PolynomialSite A B)ᵒᵖ (ModuleCat.{u} B)]
variable [HasDerivedCategory.{q'} (ModuleCat.{u} B)]
variable [HasDerivedCategory.{q} ((Algebra.PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B)]
variable [Functor.HasLeftDerivedFunctor
  (categoryOverPointColimitToDerived (Algebra.PolynomialSite A B) (ModuleCat.{u} B))
  (HomotopyCategory.quasiIso ((Algebra.PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B)
    (ComplexShape.up ℤ))]

/-- The canonical derived constant-colimit counit on the polynomial site of any commutative
ring map is invertible. -/
@[stacks 08QE]
instance Algebra.PolynomialSite.lowerShriek_inverseImage_isIso :
    IsIso
      (derivedColimitCounit :
        (derivedConstant :
            DerivedCategory.{q'} (ModuleCat.{u} B) ⥤
              DerivedCategory.{q} ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B)) ⋙
          Lπ![(PolynomialSite A B), (ModuleCat.{u} B)] ⟶
            𝟭 (DerivedCategory.{q'} (ModuleCat.{u} B))) := sorry

/-- Derived lower shriek recovers a derived module from its constant diagram on the
polynomial site. -/
theorem Algebra.PolynomialSite.lowerShriek_inverseImage_obj (M : DerivedCategory (ModuleCat.{u} B)) :
    IsIsomorphic
      ((Lπ![(PolynomialSite A B), (ModuleCat.{u} B)]).obj
        ((derivedConstant :
            DerivedCategory.{q'} (ModuleCat.{u} B) ⥤
              DerivedCategory.{q} ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B)).obj M))
      M := sorry

/-- Derived lower shriek recovers a module concentrated in degree zero from its constant
diagram on the polynomial site. -/
theorem Algebra.PolynomialSite.lowerShriek_inverseImage_single (M : ModuleCat.{u} B) :
    IsIsomorphic
      ((Lπ![(PolynomialSite A B), (ModuleCat.{u} B)]).obj
        ((derivedConstant :
            DerivedCategory.{q'} (ModuleCat.{u} B) ⥤
              DerivedCategory.{q} ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B)).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} B) (0 : ℤ)).obj M)))
      ((DerivedCategory.singleFunctor (ModuleCat.{u} B) (0 : ℤ)).obj M) := sorry
