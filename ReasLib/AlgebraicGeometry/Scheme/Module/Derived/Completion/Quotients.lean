module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.ConstantCompletion
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.CompletionMap
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.PseudoCoherent
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Sections
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.IdealSubobject
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.RingedSpace
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory CategoryTheory.Limits RingedSite.Hom.ModuleDerived
open SheafOfModules.RingedSite.IdealSheaf

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived.DerivedCompletion

/-- A derived completion is a homotopy limit of the positive
tower of derived ideal-power quotients. -/
@[stacks 0A0K]
theorem isOfQuotientTower {X : Scheme.{u}} [IsLocallyNoetherian X]
    (𝓘 : X.IdealSheafData) [𝓘.toModule.IsQuasicoherent]
    {K Khat : DerivedCategory X.Modules}
    (η : K ⟶ Khat) (hη : IsDerivedCompletion.{u, u, u, u} 𝓘.toSubobject η) :
    HomotopyLimit.IsOf (RingedSite.Hom.ModuleDerived.ConstantCompletion.completionQuotientTower.{u} 𝓘.toSubobject K) Khat := sorry

/-- The cohomology sheaf of the derived completion of a
pseudo-coherent derived module is the inverse limit of its positive ideal-power
quotient tower. -/
@[stacks 0A0K]
theorem cohomologySheafIsIsomorphicLimit {X : Scheme.{u}} [IsLocallyNoetherian X]
    (𝓘 : X.IdealSheafData) [𝓘.toModule.IsQuasicoherent]
    {K Khat : DerivedCategory X.Modules}
    (hK : RingedSpace.ModuleDerived.IsPseudoCoherent K) (η : K ⟶ Khat)
    (hη : IsDerivedCompletion.{u, u, u, u} 𝓘.toSubobject η) (q : ℤ) :
    IsIsomorphic (RingedSpace.ModuleDerived.cohomologySheaf Khat q)
      (limit (CategoryTheory.SequentialInverseSystem.shift
        (PowerQuotientModule.system.{u, u, u} 𝓘.toSubobject
          (RingedSpace.ModuleDerived.cohomologySheaf K q)) 1)) := sorry

/-- The derived completion of a coherent module is the
degree-zero object on the inverse limit of its positive ideal-power quotients. -/
@[stacks 0A0K]
theorem coherentIsIsomorphicLimit {X : Scheme.{u}} [IsLocallyNoetherian X]
    (𝓘 : X.IdealSheafData) [𝓘.toModule.IsQuasicoherent]
    (F : X.Modules) [F.IsCoherent]
    {Fhat : DerivedCategory X.Modules}
    (η : (DerivedCategory.singleFunctor X.Modules (0 : ℤ)).obj F ⟶ Fhat)
    (hη : IsDerivedCompletion.{u, u, u, u} 𝓘.toSubobject η) :
    IsIsomorphic Fhat
      ((DerivedCategory.singleFunctor X.Modules (0 : ℤ)).obj
        ((Scheme.Modules.fromRingedSpace X).obj
          (limit (CategoryTheory.SequentialInverseSystem.shift
            (PowerQuotientModule.system.{u, u, u} 𝓘.toSubobject F) 1)))) := sorry

/-- The ordinary inverse limit of the positive ideal-power
quotient tower of a coherent module computes its homotopy limit. -/
@[stacks 0A0K]
theorem coherentLimitIsOf {X : Scheme.{u}} [IsLocallyNoetherian X]
    (𝓘 : X.IdealSheafData) [𝓘.toModule.IsQuasicoherent]
    (F : X.Modules) [F.IsCoherent] :
    HomotopyLimit.IsOf
      ((CategoryTheory.SequentialInverseSystem.shift
        (PowerQuotientModule.system.{u, u, u} 𝓘.toSubobject F) 1) ⋙
        Scheme.Modules.fromRingedSpace X ⋙
          DerivedCategory.singleFunctor X.Modules (0 : ℤ))
      ((DerivedCategory.singleFunctor X.Modules (0 : ℤ)).obj
        ((Scheme.Modules.fromRingedSpace X).obj
          (limit (CategoryTheory.SequentialInverseSystem.shift
            (PowerQuotientModule.system.{u, u, u} 𝓘.toSubobject F) 1)))) := sorry

/-- A derived completion of a coherent module has zero
hypercohomology in every nonzero integer degree on every affine open. -/
@[stacks 0A0K]
theorem coherentHigherCohomologyIsZero {X : Scheme.{u}} [IsLocallyNoetherian X]
    (𝓘 : X.IdealSheafData) [𝓘.toModule.IsQuasicoherent]
    (F : X.Modules) [F.IsCoherent]
    {Fhat : DerivedCategory X.Modules}
    (η : (DerivedCategory.singleFunctor X.Modules (0 : ℤ)).obj F ⟶ Fhat)
    (hη : IsDerivedCompletion.{u, u, u, u} 𝓘.toSubobject η)
    (U : X.affineOpens) (p : ℤ) (hp : p ≠ 0) :
    IsZero (RingedSpace.moduleOpenHypercohomology X.toRingedSpace U Fhat p) := sorry

end AlgebraicGeometry.Scheme.ModuleDerived.DerivedCompletion

end
