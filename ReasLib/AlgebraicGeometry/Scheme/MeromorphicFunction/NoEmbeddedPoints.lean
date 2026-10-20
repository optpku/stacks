/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.EmbeddedPoints.GenericPoints
public import ReasLib.AlgebraicGeometry.Scheme.MeromorphicFunction.FiniteComponents

/-!
# Meromorphic functions on locally Noetherian schemes without embedded points

The absence of embedded points identifies the weakly associated points with generic points
well enough to specialize the finite-component description of meromorphic functions.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.MeromorphicFunction.NoEmbeddedPoints

/-- On a locally Noetherian scheme without embedded points, the meromorphic-function sheaf is
isomorphic to the product of the pushed-forward local-ring sheaves at the generic points. -/
theorem sheaf_iso_genericPointStalkPushforwardProduct
    (X : Scheme.{u}) [IsLocallyNoetherian X]
    (hembedded : X.embeddedPoints = (∅ : Set X)) :
    IsIsomorphic X.toLocallyRingedSpace.meromorphicFunctionSheaf
      (genericPointStalkPushforwardProductSheaf X) := sorry

/-- On a locally Noetherian scheme without embedded points, the meromorphic-function algebra
is quasicoherent as a module over the structure sheaf. -/
theorem sheaf_isQuasicoherent
    (X : Scheme.{u}) [IsLocallyNoetherian X]
    (hembedded : X.embeddedPoints = (∅ : Set X)) :
    ((restrictionAlong X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom).obj
      (SheafOfModules.unit
        (ringSheaf (Opens.grothendieckTopology X.toTopCat)
          X.toLocallyRingedSpace.meromorphicFunctionSheaf) :
        ringedSiteModuleCategory (Opens.grothendieckTopology X.toTopCat)
          X.toLocallyRingedSpace.meromorphicFunctionSheaf)).IsQuasicoherent := sorry

/-- On a locally Noetherian scheme without embedded points, the rational-function ring is
isomorphic to the ring of global meromorphic functions. -/
theorem rationalFunctionRing_iso_meromorphicFunctions
    (X : Scheme.{u}) [IsLocallyNoetherian X]
    (hembedded : X.embeddedPoints = (∅ : Set X)) :
    IsIsomorphic X.rationalFunctionRing X.toLocallyRingedSpace.meromorphicFunctions := sorry

end AlgebraicGeometry.Scheme.MeromorphicFunction.NoEmbeddedPoints
