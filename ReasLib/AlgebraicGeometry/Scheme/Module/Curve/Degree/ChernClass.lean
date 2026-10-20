/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.Degree
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.RankDecomposition
public import ReasLib.AlgebraicGeometry.CycleGroup.Fundamental
public import ReasLib.AlgebraicGeometry.ChowGroup.Degree

/-!
# Curve degrees and first Chern classes

This module compares the degree of a finite locally free module on a proper curve with the
Chow degree of its first Chern class capped with the fundamental cycle.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The first Chern class of a finite locally free module capped with the degree-one fundamental
class of a scheme over a field. -/
noncomputable def firstChernClassCapFundamental
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (E : X.left.Modules)
    [E.IsFiniteLocallyFree] :
    RelativeChow (fun _ : Spec (CommRingCat.of k) ↦ 0) (Over.mk X.hom) 0 :=
  ((ChernClass.chernClass (fun _ : Spec (CommRingCat.of k) ↦ 0) X.hom E 1).cap
    (𝟙 (Over.mk X.hom)) (𝟙 (Over.mk X.hom)) (𝟙 (Over.mk X.hom))
    IsPullback.of_id_snd 1
    (@chowClass X.left
      -- Local instance justification (defeq pin): align the degree-one class with `curveDegree` and `RelativeChow`.
      (@LocallyOfFiniteType.isLocallyNoetherian _ _ X.hom inferInstance
        (@instIsLocallyNoetherianSpecOfIsNoetherianRingCarrier
          (CommRingCat.of k) PrincipalIdealRing.isNoetherianRing))
      (X.hom.relativeDimensionFunction (fun _ : Spec (CommRingCat.of k) ↦ 0))
      inferInstance 1
      (@CycleGroup.fundamental X.left
        -- Local instance justification (defeq pin): align the fundamental class with `curveDegree` and `RelativeChow`.
        (@LocallyOfFiniteType.isLocallyNoetherian _ _ X.hom inferInstance
          (@instIsLocallyNoetherianSpecOfIsNoetherianRingCarrier
            (CommRingCat.of k) PrincipalIdealRing.isNoetherianRing))
        (X.hom.relativeDimensionFunction (fun _ : Spec (CommRingCat.of k) ↦ 0)) 1)))

/-- The degree of a constant-rank finite locally free module on a proper scheme over a field of
dimension at most one is the Chow degree of its first Chern class capped with the degree-one
fundamental class. -/
theorem curveDegree_eq_chowDegree_firstChernClassCap
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1)
    (E : X.left.Modules) (n : ℕ) [E.IsFiniteLocallyFreeOfRank n] :
    curveDegree X.hom hdim E n =
      ChowGroup.degree X (firstChernClassCapFundamental X E) := sorry

/-- For a proper scheme of dimension at most one over a field, the Euler characteristic of a
finite locally free module is its first-Chern-class degree plus its rank times the Euler
characteristic of the structure sheaf. -/
theorem curveRiemannRoch
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1)
    (E : X.left.Modules) (n : ℕ) [E.IsFiniteLocallyFreeOfRank n] :
    -- Local instance justification (defeq pin): the canonical properness-induced Noetherian structure aligns coherence inference for the Euler characteristics with curveDegree.
    let _ : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
    Scheme.Hom.eulerCharacteristic X.hom E =
      ChowGroup.degree X (firstChernClassCapFundamental X E) +
        (n : ℤ) * Scheme.Hom.eulerCharacteristic X.hom
          (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) := sorry

end AlgebraicGeometry.Scheme.Modules
