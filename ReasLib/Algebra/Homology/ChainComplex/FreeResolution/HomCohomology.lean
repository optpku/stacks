/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Abelian.Projective.Extend
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.ChainComplex.FreeResolution
public import ReasLib.Algebra.Homology.CochainComplex.HomComplex.Precomposition

@[expose] public section

/-!
# Hom Cohomology of Free Resolutions

@stack 00LT

This leaf packages the contravariant map on Hom cohomology induced by a
compatible map of free resolutions and records its independence and
isomorphism properties.
-/

open CategoryTheory

noncomputable section

universe u v

namespace ChainComplex.IsFreeResolution

variable {R : Type u} [Ring R]
variable {M₁ M₂ N : Type v}
variable [AddCommGroup M₁] [Module R M₁]
variable [AddCommGroup M₂] [Module R M₂]
variable [AddCommGroup N] [Module R N]
variable {F G : ChainComplex (ModuleCat R) ℕ}

/-- The compatible projective-resolution lift of the identity map. -/
noncomputable def identityLift
    {piF : F ⟶ moduleSingle R M₁} [IsFreeResolution piF] :
    ProjectiveResolution.Hom (toProjectiveResolution piF) (toProjectiveResolution piF)
      (𝟙 (ModuleCat.of R M₁)) := sorry

/-- Compose two compatible projective-resolution lifts. -/
noncomputable def compLift
    {M₃ : Type v} [AddCommGroup M₃] [Module R M₃]
    {H : ChainComplex (ModuleCat R) ℕ}
    {piF : F ⟶ moduleSingle R M₁} {piG : G ⟶ moduleSingle R M₂}
    {piH : H ⟶ moduleSingle R M₃}
    [IsFreeResolution piF] [IsFreeResolution piG] [IsFreeResolution piH]
    {f : ModuleCat.of R M₁ ⟶ ModuleCat.of R M₂}
    {g : ModuleCat.of R M₂ ⟶ ModuleCat.of R M₃}
    (alpha : ProjectiveResolution.Hom (toProjectiveResolution piF)
      (toProjectiveResolution piG) f)
    (beta : ProjectiveResolution.Hom (toProjectiveResolution piG)
      (toProjectiveResolution piH) g) :
    ProjectiveResolution.Hom (toProjectiveResolution piF) (toProjectiveResolution piH) (f ≫ g) :=
  sorry

/-- The compatible lift of the inverse of an isomorphism. -/
noncomputable def inverseLift
    (f : ModuleCat.of R M₁ ⟶ ModuleCat.of R M₂) [IsIso f]
    (piF : F ⟶ moduleSingle R M₁) (piG : G ⟶ moduleSingle R M₂)
    [IsFreeResolution piF] [IsFreeResolution piG] :
    ProjectiveResolution.Hom (toProjectiveResolution piG) (toProjectiveResolution piF) (inv f) :=
  sorry

/-- The map on the cohomology of `Hom_R(-, N)` induced by a compatible lift between free
resolutions. -/
noncomputable def homologyMap
    {piF : F ⟶ moduleSingle R M₁} {piG : G ⟶ moduleSingle R M₂}
    [IsFreeResolution piF] [IsFreeResolution piG]
    {f : ModuleCat.of R M₁ ⟶ ModuleCat.of R M₂}
    (alpha : ProjectiveResolution.Hom (toProjectiveResolution piF)
      (toProjectiveResolution piG) f) (N : Type v) [AddCommGroup N] [Module R N] (i : ℤ) :=
  HomologicalComplex.homologyMap
    (CochainComplex.homComplexPrecomp (f := alpha.hom')
      (I := (CochainComplex.singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R N))) i

/-- Lemma 10.71.5 (1) (00LT): compatible lifts of the same module map induce the same map on
the cohomology of `Hom_R(-, N)`. -/
@[stacks 00LT "(1), independence of the compatible lift"]
theorem homologyMap_eq_of_compatibleLifts
    (f : ModuleCat.of R M₁ ⟶ ModuleCat.of R M₂)
    (piF : F ⟶ moduleSingle R M₁) (piG : G ⟶ moduleSingle R M₂)
    [IsFreeResolution piF] [IsFreeResolution piG]
    (alpha beta : ProjectiveResolution.Hom (toProjectiveResolution piF)
      (toProjectiveResolution piG) f) (i : ℤ) :
    homologyMap alpha N i = homologyMap beta N i := sorry

/-- Lemma 10.71.5 (2) (00LT): a lift of a module isomorphism induces an isomorphism on every
`Hom_R(-, N)` cohomology group. -/
@[stacks 00LT "(2), isomorphism induced by a lifted isomorphism"]
theorem homologyMap_isIso_of_isIso
    (f : ModuleCat.of R M₁ ⟶ ModuleCat.of R M₂) [IsIso f]
    (piF : F ⟶ moduleSingle R M₁) (piG : G ⟶ moduleSingle R M₂)
    [IsFreeResolution piF] [IsFreeResolution piG]
    (alpha : ProjectiveResolution.Hom (toProjectiveResolution piF)
      (toProjectiveResolution piG) f) (i : ℤ) :
    IsIso (homologyMap alpha N i) := sorry

/-- Lemma 10.71.5 (3) (00LT): a compatible lift of the identity induces the identity on every
`Hom_R(-, N)` cohomology group. -/
@[stacks 00LT "(3), identity induced by an identity lift"]
theorem homologyMap_eq_id
    (piF : F ⟶ moduleSingle R M₁) [IsFreeResolution piF]
    (alpha : ProjectiveResolution.Hom (toProjectiveResolution piF)
      (toProjectiveResolution piF) (𝟙 (ModuleCat.of R M₁))) (i : ℤ) :
    homologyMap alpha N i = 𝟙 _ := sorry

end ChainComplex.IsFreeResolution
