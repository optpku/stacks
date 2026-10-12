/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.MeromorphicSection

/-!
# Meromorphic sections reconstructed from generic germs

On an integral scheme, an element of the generic stalk of an invertible module determines a
meromorphic section. This file supplies that construction and its characterizing properties.
-/

@[expose] public section

open Function
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The meromorphic section whose canonical generic germ is induced by an element of the
generic stalk of an invertible module on an integral scheme. -/
noncomputable def meromorphicSectionOfGenericGerm {X : Scheme.{u}} [IsIntegral X]
    (lineBundle : X.Modules) [Invertible lineBundle]
    (germ : RingedSpace.stalkModuleCat lineBundle (genericPoint X)) :
    X.toLocallyRingedSpace.meromorphicSections lineBundle :=
  Function.invFun
    (fun section_ : X.toLocallyRingedSpace.meromorphicSections lineBundle ↦
      SheafOfModules.sectionGermOfCommRing section_ (genericPoint X))
    (X.toLocallyRingedSpace.meromorphicSectionStalkMap lineBundle (genericPoint X) germ)

/-- The selected meromorphic section has the canonical meromorphic-stalk image of the supplied
generic germ. -/
theorem meromorphicSectionOfGenericGerm_spec {X : Scheme.{u}} [IsIntegral X]
    (lineBundle : X.Modules) [Invertible lineBundle]
    (germ : RingedSpace.stalkModuleCat lineBundle (genericPoint X)) :
    SheafOfModules.sectionGermOfCommRing
        (meromorphicSectionOfGenericGerm lineBundle germ) (genericPoint X) =
      X.toLocallyRingedSpace.meromorphicSectionStalkMap
        lineBundle (genericPoint X) germ := sorry

/-- A meromorphic section with the prescribed canonical generic germ is the selected section;
thus the construction is independent of the choice made by `Function.invFun`. -/
theorem meromorphicSectionOfGenericGerm_unique {X : Scheme.{u}} [IsIntegral X]
    (lineBundle : X.Modules) [Invertible lineBundle]
    (germ : RingedSpace.stalkModuleCat lineBundle (genericPoint X))
    (section_ : X.toLocallyRingedSpace.meromorphicSections lineBundle)
    (hsection : SheafOfModules.sectionGermOfCommRing section_ (genericPoint X) =
      X.toLocallyRingedSpace.meromorphicSectionStalkMap
        lineBundle (genericPoint X) germ) :
    section_ = meromorphicSectionOfGenericGerm lineBundle germ := sorry

/-- The meromorphic section selected from a generic germ vanishes exactly when the germ does. -/
theorem meromorphicSectionOfGenericGerm_eq_zero_iff {X : Scheme.{u}} [IsIntegral X]
    (lineBundle : X.Modules) [Invertible lineBundle]
    (germ : RingedSpace.stalkModuleCat lineBundle (genericPoint X)) :
    meromorphicSectionOfGenericGerm lineBundle germ = 0 ↔ germ = 0 := sorry

end AlgebraicGeometry.Scheme.Modules
