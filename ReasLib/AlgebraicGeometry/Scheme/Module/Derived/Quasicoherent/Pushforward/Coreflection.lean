/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Comparison
import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Adjunction
import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pullback
import ReasLib.CategoryTheory.Adjunction.RightIso
import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction.Adjunction

/-!
# Derived pushforward and quasicoherent coreflections

This module records the compatibility of derived pushforward with right adjoints to the
inclusions of derived modules having quasicoherent cohomology.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- For a quasi-compact and quasi-separated morphism of schemes, restricted derived pushforward
after the source quasicoherent coreflection is naturally isomorphic to ambient derived
pushforward followed by the target quasicoherent coreflection. -/
theorem pushforward_comp_rightAdjoint_isomorphic {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    [(DerivedCategory.cohomologyIn
      (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).ι.IsLeftAdjoint]
    [(DerivedCategory.cohomologyIn
      (RingedSpace.quasiCoherentModuleProperty Y.toRingedSpace)).ι.IsLeftAdjoint] :
    IsIsomorphic
      ((DerivedCategory.cohomologyIn
          (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).ι.rightAdjoint ⋙
        pushforwardCohomologyIn f)
      (RingedSpace.moduleDerivedPushforward f.toShHom ⋙
        (DerivedCategory.cohomologyIn
          (RingedSpace.quasiCoherentModuleProperty Y.toRingedSpace)).ι.rightAdjoint) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
