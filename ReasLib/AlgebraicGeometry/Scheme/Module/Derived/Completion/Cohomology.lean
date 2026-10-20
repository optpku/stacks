/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Completeness
public import ReasLib.Algebra.Module.IdealPower.Quotient
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.PseudoCoherent
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Sections
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.CompletionMap
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.IdealSubobject
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Basic
public import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory CategoryTheory.Limits RingedSite.Hom.ModuleDerived

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace ModuleDerived
namespace DerivedCompletion

variable {X : Scheme.{u}} [IsLocallyNoetherian X]
variable (𝓘 : X.IdealSheafData) [𝓘.toModule.IsQuasicoherent]

/-- On an affine open of a locally Noetherian scheme, cohomology of an ideal-sheaf derived
completion of a pseudo-coherent complex is the inverse limit of its positive quotient tower. -/
@[stacks 0A0L]
theorem cohomologyIsIsomorphicLimit
    {K Khat : DerivedCategory X.Modules}
    (hK : RingedSpace.ModuleDerived.IsPseudoCoherent K) (η : K ⟶ Khat)
    (hη : IsDerivedCompletion.{u, u, u, u}
      𝓘.toSubobject η)
    (U : X.affineOpens) (p : ℤ) :
    IsIsomorphic
      ((DerivedCategory.homologyFunctor (ModuleCat Γ(X, U)) p).obj
        ((RingedSpace.moduleDerivedSectionsAtOpen X.toRingedSpace U).obj Khat))
      (limit (Ideal.PowerQuotient.positiveSystem (𝓘.ideal U)
        ((DerivedCategory.homologyFunctor (ModuleCat Γ(X, U)) p).obj
          ((RingedSpace.moduleDerivedSectionsAtOpen X.toRingedSpace U).obj K)))) := sorry

/-- On an affine open of a locally Noetherian scheme, the positive quotient limit in degree zero
is the derived completion of the degree-`p` cohomology module placed in degree zero. -/
@[stacks 0A0L]
theorem limitIsIsomorphicCompletedCohomology
    {K : DerivedCategory X.Modules}
    (hK : RingedSpace.ModuleDerived.IsPseudoCoherent K)
    (U : X.affineOpens) (p : ℤ) :
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
            ((RingedSpace.moduleDerivedSectionsAtOpen X.toRingedSpace U).obj K)))) := sorry

end DerivedCompletion
end ModuleDerived
end Scheme
end AlgebraicGeometry
