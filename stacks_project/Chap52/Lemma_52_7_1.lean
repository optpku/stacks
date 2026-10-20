/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Completeness.Cohomology
public import ReasLib.Algebra.Module.IdealPower.Quotient
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.PseudoCoherent
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Sections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Completion.Cohomology
public import stacks_project.Chap52.Remark_52_6_21
public import Mathlib.AlgebraicGeometry.Noetherian
import StacksCheckRecall
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory CategoryTheory.Limits RingedSite.Hom.ModuleDerived
open AlgebraicGeometry

universe u

/- Lemma 52.7.1: on an affine open, cohomology of a pseudo-coherent derived completion is the
inverse limit of the positive ideal-power quotient tower; this limit in degree zero is the derived
completion of the degree-`p` cohomology module placed in degree zero. -/
@[stacks 0A0L] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.DerivedCompletion.cohomologyIsIsomorphicLimit :
    ∀ {X : Scheme.{u}} [IsLocallyNoetherian X]
      (𝓘 : X.IdealSheafData) [𝓘.toModule.IsQuasicoherent]
      {K Khat : DerivedCategory X.Modules}
      (hK : RingedSpace.ModuleDerived.IsPseudoCoherent K) (η : K ⟶ Khat)
      (hη : IsDerivedCompletion.{u, u, u, u} 𝓘.toSubobject η)
      (U : X.affineOpens) (p : ℤ),
      IsIsomorphic
        ((DerivedCategory.homologyFunctor (ModuleCat Γ(X, U)) p).obj
          ((RingedSpace.moduleDerivedSectionsAtOpen X.toRingedSpace U).obj Khat))
        (limit (Ideal.PowerQuotient.positiveSystem (𝓘.ideal U)
          ((DerivedCategory.homologyFunctor (ModuleCat Γ(X, U)) p).obj
            ((RingedSpace.moduleDerivedSectionsAtOpen X.toRingedSpace U).obj K)))))

/- The degree-zero realization of the quotient limit is the full derived completion of the degree-`p`
cohomology module. -/
@[stacks 0A0L] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.DerivedCompletion.limitIsIsomorphicCompletedCohomology :
    ∀ {X : Scheme.{u}} [IsLocallyNoetherian X]
      (𝓘 : X.IdealSheafData) [𝓘.toModule.IsQuasicoherent]
      {K : DerivedCategory X.Modules}
      (hK : RingedSpace.ModuleDerived.IsPseudoCoherent K)
      (U : X.affineOpens) (p : ℤ),
      IsIsomorphic
        ((DerivedCategory.singleFunctor (ModuleCat Γ(X, U)) (0 : ℤ)).obj
          (limit (Ideal.PowerQuotient.positiveSystem (𝓘.ideal U)
            ((DerivedCategory.homologyFunctor (ModuleCat Γ(X, U)) p).obj
              ((RingedSpace.moduleDerivedSectionsAtOpen X.toRingedSpace U).obj K)))))
        (DerivedCategory.derivedCompletionOf (𝓘.ideal U)
          ((isNoetherianRing_iff_ideal_fg (Γ(X, U))).mp
            (IsLocallyNoetherian.component_noetherian U) (𝓘.ideal U))
          ((DerivedCategory.singleFunctor (ModuleCat Γ(X, U)) (0 : ℤ)).obj
            ((DerivedCategory.homologyFunctor (ModuleCat Γ(X, U)) p).obj
              ((RingedSpace.moduleDerivedSectionsAtOpen X.toRingedSpace U).obj K)))))
