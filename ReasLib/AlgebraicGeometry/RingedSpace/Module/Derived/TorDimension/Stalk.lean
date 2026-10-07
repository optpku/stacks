module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Tensor
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TorDimension
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Stalk
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Stalk.Exact
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Stalkwise Tor-amplitude

The ringed-space stalk is modeled by the canonical module stalk functor. Its exactness and the
module-category derived tensor structure provide a canonical presentation of derived stalks and
their Tor-amplitude.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived.Stalk

variable {X : RingedSpace.{u}}

/-- The canonical additive structure on the module stalk functor. -/
@[stacks 09U9 "additive module stalk", instance]
noncomputable instance functor_additive (x : X) :
    (RingedSpace.stalkModuleFunctor x).Additive := sorry

/-- The module stalk functor preserves finite limits. -/
@[stacks 09U9 "finite-limit exactness of module stalk", instance]
noncomputable instance functor_preservesFiniteLimits (x : X) :
    PreservesFiniteLimits (RingedSpace.stalkModuleFunctor x) := sorry

/-- The module stalk functor preserves finite colimits. -/
@[stacks 09U9 "finite-colimit exactness of module stalk", instance]
noncomputable instance functor_preservesFiniteColimits (x : X) :
    PreservesFiniteColimits (RingedSpace.stalkModuleFunctor x) := sorry

/-- The derived module stalk functor at `x : X`. -/
@[stacks 09U9 "derived module stalk"]
noncomputable abbrev functor (x : X) :
    RingedSpace.ModuleDerived X ⥤
      DerivedCategory (ModuleCat (X.presheaf.stalk x)) :=
  (RingedSpace.stalkModuleFunctor x).mapDerivedCategory

/-- The object obtained by taking the derived module stalk of `E` at `x`. -/
@[stacks 09U9 "derived module stalk object"]
noncomputable abbrev obj (E : RingedSpace.ModuleDerived X) (x : X) :
    DerivedCategory (ModuleCat (X.presheaf.stalk x)) :=
  (functor x).obj E

/-- Tor-amplitude on a ringed space is detected on all derived stalks. -/
@[stacks 09U9]
theorem hasTorAmplitudeIn_iff
    (E : RingedSpace.ModuleDerived X) (a b : ℤ) :
    RingedSpace.HasTorAmplitudeIn E a b ↔
      ∀ x : X,
        CategoryTheory.DerivedCategory.DerivedTensor.HasTorAmplitudeIn
          (obj E x) a b := sorry

namespace HasTorAmplitudeIn

/-- A global Tor-amplitude bound gives the corresponding bound at every stalk. -/
theorem forall_stalk
    {E : RingedSpace.ModuleDerived X} {a b : ℤ}
    (hE : RingedSpace.HasTorAmplitudeIn E a b) :
  ∀ x : X,
      CategoryTheory.DerivedCategory.DerivedTensor.HasTorAmplitudeIn
        (obj E x) a b :=
  (AlgebraicGeometry.RingedSpace.ModuleDerived.Stalk.hasTorAmplitudeIn_iff E a b).1 hE

/-- Stalkwise Tor-amplitude bounds glue to a global bound. -/
theorem of_forall_stalk
    {E : RingedSpace.ModuleDerived X} {a b : ℤ}
    (hE : ∀ x : X,
      CategoryTheory.DerivedCategory.DerivedTensor.HasTorAmplitudeIn
        (obj E x) a b) :
    RingedSpace.HasTorAmplitudeIn E a b :=
  (AlgebraicGeometry.RingedSpace.ModuleDerived.Stalk.hasTorAmplitudeIn_iff E a b).2 hE

end HasTorAmplitudeIn

end AlgebraicGeometry.RingedSpace.ModuleDerived.Stalk
