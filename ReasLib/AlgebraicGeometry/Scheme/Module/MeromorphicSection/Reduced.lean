module

public import ReasLib.AlgebraicGeometry.Scheme.MeromorphicFunction.Reduced
public import ReasLib.AlgebraicGeometry.Scheme.Module.MeromorphicSection.FiniteComponents

/-!
# Meromorphic sections on reduced schemes

On a reduced scheme with finitely many irreducible components on quasi-compact opens,
meromorphic sections of a quasicoherent module are described by the pushed-forward stalks at
the generic points.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Module.MeromorphicSection.Reduced

/-- The canonical comparison between the meromorphic-section sheaf of a quasicoherent module on
a reduced scheme and the product of its pushed-forward generic-point stalks. -/
noncomputable def sheafIsoGenericPointStalkPushforwardProduct
    (X : Scheme.{u}) [IsReduced X]
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    ((restrictionAlong X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom).obj
        (X.toLocallyRingedSpace.meromorphicSectionSheaf ℱ)) ≅
      genericPointStalkPushforwardProductModule X ℱ :=
  Classical.choice
    (meromorphicSectionSheaf_isIsomorphic_genericPointStalkPushforwardProduct X
      (Scheme.weakAss_eq_genericPoints X).le ℱ)

/-- On a reduced scheme with locally finite irreducible components, meromorphic sections of a
quasicoherent module are isomorphic to the product of the pushed-forward generic-point stalks. -/
theorem sheaf_isIsomorphic_genericPointStalkPushforwardProduct
    (X : Scheme.{u}) [IsReduced X]
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    IsIsomorphic
      ((restrictionAlong X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom).obj
        (X.toLocallyRingedSpace.meromorphicSectionSheaf ℱ))
      (genericPointStalkPushforwardProductModule X ℱ) :=
  ⟨sheafIsoGenericPointStalkPushforwardProduct X ℱ⟩

/-- On a reduced scheme with locally finite irreducible components, meromorphic sections of a
quasicoherent module are isomorphic to the coproduct of the pushed-forward generic-point
stalks. -/
theorem sheaf_isIsomorphic_genericPointStalkPushforwardCoproduct
    (X : Scheme.{u}) [IsReduced X]
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    IsIsomorphic
      ((restrictionAlong X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom).obj
        (X.toLocallyRingedSpace.meromorphicSectionSheaf ℱ))
      (genericPointStalkPushforwardCoproductModule X ℱ) := sorry

/-- On a reduced scheme with locally finite irreducible components, meromorphic sections of a
quasicoherent module are quasicoherent over the structure sheaf. -/
theorem sheaf_isQuasicoherent
    (X : Scheme.{u}) [IsReduced X]
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    ((restrictionAlong X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom).obj
      (X.toLocallyRingedSpace.meromorphicSectionSheaf ℱ)).IsQuasicoherent := sorry

end AlgebraicGeometry.Scheme.Module.MeromorphicSection.Reduced
