/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.MeromorphicFunction.NoEmbeddedPoints
public import ReasLib.AlgebraicGeometry.Scheme.Module.MeromorphicSection.FiniteComponents

/-!
# Meromorphic sections on locally Noetherian schemes without embedded points

For a quasicoherent module, the finite-component description of meromorphic sections applies
when the ambient scheme is locally Noetherian and has no embedded points.
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Module.MeromorphicSection.NoEmbeddedPoints

/-- On a locally Noetherian scheme without embedded points, the meromorphic-section sheaf of a
quasicoherent module is isomorphic to the product of its pushed-forward generic-point stalks. -/
theorem sheaf_isIsomorphic_genericPointStalkPushforwardProduct
    (X : Scheme.{u}) [IsLocallyNoetherian X]
    (hembedded : X.embeddedPoints = (∅ : Set X))
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    IsIsomorphic
      ((restrictionAlong X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom).obj
        (X.toLocallyRingedSpace.meromorphicSectionSheaf ℱ))
      (genericPointStalkPushforwardProductModule X ℱ) := sorry

/-- On a locally Noetherian scheme without embedded points, the meromorphic-section sheaf of a
quasicoherent module is quasicoherent over the structure sheaf. -/
theorem sheaf_isQuasicoherent
    (X : Scheme.{u}) [IsLocallyNoetherian X]
    (hembedded : X.embeddedPoints = (∅ : Set X))
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    ((restrictionAlong X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom).obj
      (X.toLocallyRingedSpace.meromorphicSectionSheaf ℱ)).IsQuasicoherent := sorry

end AlgebraicGeometry.Scheme.Module.MeromorphicSection.NoEmbeddedPoints
