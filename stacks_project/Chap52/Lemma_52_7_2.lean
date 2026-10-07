module

public import stacks_project.Chap52.Lemma_52_7_1
public import stacks_project.Chap52.Remark_52_6_13_Comparison_with_completion
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.RingedSpace
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory CategoryTheory.Limits RingedSite.Hom.ModuleDerived
open SheafOfModules.RingedSite.IdealSheaf

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace ModuleDerived
namespace DerivedCompletion

variable {X : Scheme.{u}} [IsLocallyNoetherian X]
variable [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
variable (𝓘 : X.IdealSheafData) [𝓘.toModule.IsQuasicoherent]

/-- Lemma 52.7.2 (1): a derived completion is a homotopy limit of the positive
tower of derived ideal-power quotients. -/
@[stacks 0A0K]
theorem isOfQuotientTower {K Khat : DerivedCategory X.Modules}
    (η : K ⟶ Khat) (hη : IsDerivedCompletion.{u, u, u, u} 𝓘.toSubobject η) :
    HomotopyLimit.IsOf (completionQuotientTower.{u} 𝓘.toSubobject K) Khat := sorry

/-- Lemma 52.7.2 (2): the cohomology sheaf of the derived completion of a
pseudo-coherent derived module is the inverse limit of its positive ideal-power
quotient tower. -/
@[stacks 0A0K]
theorem cohomologySheafIsIsomorphicLimit
    {K Khat : DerivedCategory X.Modules}
    (hK : RingedSpace.ModuleDerived.IsPseudoCoherent K) (η : K ⟶ Khat)
    (hη : IsDerivedCompletion.{u, u, u, u} 𝓘.toSubobject η) (q : ℤ) :
    IsIsomorphic (RingedSpace.ModuleDerived.cohomologySheaf Khat q)
      (limit (CategoryTheory.SequentialInverseSystem.shift
        (PowerQuotientModule.system.{u, u, u} 𝓘.toSubobject
          (RingedSpace.ModuleDerived.cohomologySheaf K q)) 1)) := sorry

/-- Lemma 52.7.2 (3): the derived completion of a coherent module is the
degree-zero object on the inverse limit of its positive ideal-power quotients. -/
@[stacks 0A0K]
theorem coherentIsIsomorphicLimit (F : X.Modules) [F.IsCoherent]
    {Fhat : DerivedCategory X.Modules}
    (η : (DerivedCategory.singleFunctor X.Modules (0 : ℤ)).obj F ⟶ Fhat)
    (hη : IsDerivedCompletion.{u, u, u, u} 𝓘.toSubobject η) :
    IsIsomorphic Fhat
      ((DerivedCategory.singleFunctor X.Modules (0 : ℤ)).obj
        ((Scheme.Modules.fromRingedSpace X).obj
          (limit (CategoryTheory.SequentialInverseSystem.shift
            (PowerQuotientModule.system.{u, u, u} 𝓘.toSubobject F) 1)))) := sorry

/-- Lemma 52.7.2 (4): the ordinary inverse limit of the positive ideal-power
quotient tower of a coherent module computes its homotopy limit. -/
@[stacks 0A0K]
theorem coherentLimitIsOf (F : X.Modules) [F.IsCoherent] :
    HomotopyLimit.IsOf
      ((CategoryTheory.SequentialInverseSystem.shift
        (PowerQuotientModule.system.{u, u, u} 𝓘.toSubobject F) 1) ⋙
        Scheme.Modules.fromRingedSpace X ⋙
          DerivedCategory.singleFunctor X.Modules (0 : ℤ))
      ((DerivedCategory.singleFunctor X.Modules (0 : ℤ)).obj
        ((Scheme.Modules.fromRingedSpace X).obj
          (limit (CategoryTheory.SequentialInverseSystem.shift
            (PowerQuotientModule.system.{u, u, u} 𝓘.toSubobject F) 1)))) := sorry

/-- Lemma 52.7.2 (5): a derived completion of a coherent module has zero
positive cohomology on every affine open. -/
@[stacks 0A0K]
theorem coherentHigherCohomologyIsZero (F : X.Modules) [F.IsCoherent]
    {Fhat : DerivedCategory X.Modules}
    (η : (DerivedCategory.singleFunctor X.Modules (0 : ℤ)).obj F ⟶ Fhat)
    (hη : IsDerivedCompletion.{u, u, u, u} 𝓘.toSubobject η)
    (U : X.affineOpens) (p : ℕ) (hp : 0 < p) :
    IsZero (RingedSpace.moduleOpenHypercohomology X.toRingedSpace U Fhat (p : ℤ)) := sorry

end DerivedCompletion
end ModuleDerived
end Scheme
end AlgebraicGeometry

end
