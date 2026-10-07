module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.LocalProperties
public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.IdealSubobject.Definition
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Regularity.Conormal

/-!
# Quasi-regular ideal sheaves on locally ringed spaces

This file characterizes quasi-regular ideal sheaves using finite type, finite locally free
conormal modules, and the canonical associated-graded polynomial criterion.
-/

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

variable {X : LocallyRingedSpace.{u}}

/-- An ideal sheaf on a locally ringed space is quasi-regular exactly when it is of finite type,
its conormal module is finite locally free, and its canonical conormal-algebra map to the
associated graded algebra is bijective for every stalk ideal. -/
theorem isQuasiRegularIdealSheaf_iff (I : IdealSubobject X) :
    RingedSpace.IsQuasiRegularIdealSheaf I ↔
      I.toModule.IsFiniteType ∧
        RingedSpace.idealSheafConormalFiniteLocallyFreeCriterion I ∧
          RingedSpace.idealSheafAssociatedGradedPolynomialCriterion I := sorry

end AlgebraicGeometry.LocallyRingedSpace
