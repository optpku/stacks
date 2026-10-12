/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Completeness.Cohomology
public import ReasLib.Algebra.Module.IdealPower.Quotient
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.PseudoCoherent
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Sections
public import stacks_project.Chap52.Remark_52_6_21
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

/-- Lemma 52.7.1 (1): on an affine open, the cohomology of a pseudo-coherent
derived module's derived completion is isomorphic to the inverse limit of the
positive tower of ideal-power quotients of its cohomology. -/
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

/-- Lemma 52.7.1 (2): the inverse limit of the positive ideal-power quotient
tower of affine-open cohomology is isomorphic to degree-zero cohomology of its
derived completion. -/
@[stacks 0A0L]
theorem limitIsIsomorphicCompletedCohomology
    {K : DerivedCategory X.Modules}
    (hK : RingedSpace.ModuleDerived.IsPseudoCoherent K)
    (U : X.affineOpens) (p : ℤ) :
    IsIsomorphic
      (limit (Ideal.PowerQuotient.positiveSystem (𝓘.ideal U)
        ((DerivedCategory.homologyFunctor (ModuleCat Γ(X, U)) p).obj
          ((RingedSpace.moduleDerivedSectionsAtOpen X.toRingedSpace U).obj K))))
      ((DerivedCategory.homologyFunctor (ModuleCat Γ(X, U)) 0).obj
        (DerivedCategory.derivedCompletionOf (𝓘.ideal U)
          (@Ideal.fg_of_isNoetherianRing Γ(X, U) inferInstance
            (IsLocallyNoetherian.component_noetherian U) (𝓘.ideal U))
          ((DerivedCategory.singleFunctor (ModuleCat Γ(X, U)) 0).obj
            ((DerivedCategory.homologyFunctor (ModuleCat Γ(X, U)) p).obj
              ((RingedSpace.moduleDerivedSectionsAtOpen X.toRingedSpace U).obj K))))) := sorry

end DerivedCompletion
end ModuleDerived
end Scheme
end AlgebraicGeometry
