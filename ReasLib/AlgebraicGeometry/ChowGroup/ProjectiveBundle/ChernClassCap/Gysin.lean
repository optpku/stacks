/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.ProjectiveBundle.ChernClassCap.Intrinsic
public import ReasLib.AlgebraicGeometry.ChowGroup.Gysin.Relative

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup.ChernClassCap

/-- The grading obtained by first applying Gysin pullback and then the `j`th
Chern-class cap is the grading obtained in the opposite order. -/
theorem gysinDegree (k : ℤ) (j : ℕ) :
    (k - 1) - (j : ℤ) = (k - (j : ℤ)) - 1 := sorry

/-- Gysin pullback along the zero-scheme inclusion of a section of an invertible
module commutes with the `j`th Chern-class cap of a finite locally free module. -/
theorem gysin
    {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom]
    (E : X.left.Modules) (r : ℕ) [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (ℒ : X.left.Modules) [Scheme.Modules.Invertible ℒ] (s : ℒ.sections)
    (k : ℤ) (α : RelativeChow δ X k)
    (a : CycleGroup X.left (X.hom.relativeDimensionFunction δ) k)
    (ha : @chowClass X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
      (X.hom.relativeDimensionFunction δ) inferInstance k a = α)
    (b : CycleGroup (Scheme.zeroScheme ℒ s)
      ((Scheme.zeroSchemeι ℒ s ≫ X.hom).relativeDimensionFunction δ) (k - 1))
    (hb : @chowClass (Scheme.zeroScheme ℒ s)
      (LocallyOfFiniteType.isLocallyNoetherian (Scheme.zeroSchemeι ℒ s ≫ X.hom))
      ((Scheme.zeroSchemeι ℒ s ≫ X.hom).relativeDimensionFunction δ) inferInstance
      (k - 1) b = ChowGroup.gysin δ X ℒ s k α)
    (cX : ChernClassCap δ X.hom E r k a)
    (cD : ChernClassCap δ (Scheme.zeroSchemeι ℒ s ≫ X.hom)
      ((Scheme.Modules.pullback (Scheme.zeroSchemeι ℒ s)).obj E) r (k - 1) b)
    (j : ℕ) :
    @ChowGroup.reindex (Scheme.zeroScheme ℒ s)
        (LocallyOfFiniteType.isLocallyNoetherian (Scheme.zeroSchemeι ℒ s ≫ X.hom))
        ((Scheme.zeroSchemeι ℒ s ≫ X.hom).relativeDimensionFunction δ) inferInstance
        ((k - 1) - (j : ℤ)) ((k - (j : ℤ)) - 1) (gysinDegree k j)
        (cD.component j) =
      ChowGroup.gysin δ X ℒ s (k - (j : ℤ)) (cX.component j) := sorry

end AlgebraicGeometry.ChowGroup.ChernClassCap
