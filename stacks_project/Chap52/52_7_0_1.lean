module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.FormalFunctions

@[expose] public section

open CategoryTheory RingedSite.Hom.ModuleDerived

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace ModuleDerived
namespace DerivedCompletion

variable {X S : Scheme.{u}}

/- 52.7.0.1: For a quasi-coherent module `F`, derived pushforward carries a derived
completion of `F[0]` with respect to `I.comap f` to a derived completion of `Rf_*F`
with respect to the finite-type quasi-coherent ideal `I`. -/
@[stacks 0A0I] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.DerivedCompletion.pushforwardSingle :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) (I : S.IdealSheafData) [I.toModule.IsQuasicoherent],
      (hI : I.IsFiniteType) → (F : X.Modules) → [F.IsQuasicoherent] →
      ∀ {Khat : DerivedCategory X.Modules},
        (η : (DerivedCategory.singleFunctor X.Modules 0).obj F ⟶ Khat) →
        IsDerivedCompletion.{u, u, u, u} (I.comap f).toSubobject η →
        IsDerivedCompletion.{u, u, u, u} I.toSubobject
          ((RingedSpace.moduleDerivedPushforward f.toShHom).map η))

end DerivedCompletion
end ModuleDerived
end Scheme
end AlgebraicGeometry
