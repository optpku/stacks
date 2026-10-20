/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import stacks_project.Chap50.Remark_50_23_7_Cohomology

open AlgebraicGeometry CategoryTheory
open RingedSpace.ModuleDerived
open SheafOfModules.RingedSite.ExteriorPower
open scoped AlgebraicGeometry

universe u

/- Remark 50.23.7 (1): smoothness of `X ⟶ S` and Koszul regularity of `Z ⟶ X`
give the required lower bound on supported derived local cohomology. -/
@[stacks 0G8A] #check (@AlgebraicGeometry.Scheme.DeRham.Gysin.supportedDerivedRelativeFormIsGEOfSmoothOfKoszulRegular :
    {Z X S : Scheme.{u}} → (i : Z ⟶ X) → [IsClosedImmersion i] →
      [Scheme.Hom.FinitePresentation i] → (f : X ⟶ S) → [Smooth f] →
      [IsKoszulRegularImmersion i] → (p c : ℕ) →
      [SheafOfModules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i)] →
        (AlgebraicGeometry.Scheme.DeRham.Gysin.supportedDerived i f (p + c)).IsGE (c : ℤ))

/- Remark 50.23.7 (2): the cohomological Gysin morphism
`H^q(Z, Ω^p_{Z/S}) ⟶ H^(q+c)(X, Ω^(p+c)_{X/S})`. -/
@[stacks 0G8A] #check (@AlgebraicGeometry.Scheme.DeRham.Gysin.hodgeCohomologyMap :
    {Z X S : Scheme.{u}} → (i : Z ⟶ X) → [IsClosedImmersion i] →
      [Scheme.Hom.FinitePresentation i] → (f : X ⟶ S) → (p q c : ℕ) →
      [SheafOfModules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i)] →
      [(AlgebraicGeometry.Scheme.DeRham.Gysin.supportedDerived
        i f (p + c)).IsGE (c : ℤ)] →
        (DerivedCategory.homologyFunctor
            (ModuleCat (RingedSpace.globalSectionsRing X.toRingedSpace)) (q + c : ℤ)).obj
          ((RingedSpace.moduleSectionsRestrictionDerived i.toShHom ⊤).obj
            ((RingedSpace.Module.Derived.GlobalSections.functor Z.toRingedSpace).obj
              ((DerivedCategory.singleFunctor Z.toRingedSpace.Modules (c : ℤ)).obj
                ((Scheme.Modules.toRingedSpace Z).obj
                  (sheaf Z.𝒪 Ω[(i ≫ f).toShHom] p))))) ⟶
        (DerivedCategory.homologyFunctor
            (ModuleCat (RingedSpace.globalSectionsRing X.toRingedSpace)) (q + c : ℤ)).obj
          ((RingedSpace.Module.Derived.GlobalSections.functor X.toRingedSpace).obj
            ((ModuleCech.moduleToDerived X).obj
              ((Scheme.QCoh.inclusion X).obj
                (AlgebraicGeometry.Scheme.DeRham.Gysin.relativeFormQCoh f (p + c))))))
