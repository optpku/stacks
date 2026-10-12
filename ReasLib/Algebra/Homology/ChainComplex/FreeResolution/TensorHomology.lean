/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.CategoryTheory.Abelian.Projective.Extend
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.ChainComplex.FreeResolution.HomCohomology

@[expose] public section

/-!
# Tensor Homology of Free Resolutions

@stack 00LZ

This leaf packages the map on tensor-complex homology induced by a compatible
map of free resolutions and records its independence and isomorphism
properties.
-/

open CategoryTheory HomologicalComplex MonoidalCategory

noncomputable section

universe u

namespace ChainComplex.IsFreeResolution

variable {R : Type u} [CommRing R]
variable {M₁ M₂ : Type u}
variable [AddCommGroup M₁] [Module R M₁]
variable [AddCommGroup M₂] [Module R M₂]
variable {F G : ChainComplex (ModuleCat R) ℕ}

/-- The chain map on tensor complexes induced by a compatible map between free resolutions. -/
noncomputable def tensorComplexMap
    (N : Type u) [AddCommGroup N] [Module R N]
    {piF : F ⟶ moduleSingle R M₁} {piG : G ⟶ moduleSingle R M₂}
    [IsFreeResolution piF] [IsFreeResolution piG]
    {f : ModuleCat.of R M₁ ⟶ ModuleCat.of R M₂}
    (alpha : ProjectiveResolution.Hom (toProjectiveResolution piF)
      (toProjectiveResolution piG) f) :=
  (CategoryTheory.Functor.mapHomologicalComplex
    (tensorLeft (ModuleCat.of R N)) (ComplexShape.down ℕ)).map alpha.hom

/-- The map on tensor-complex homology induced by a compatible lift. -/
noncomputable def tensorHomologyMap
    (N : Type u) [AddCommGroup N] [Module R N]
    {piF : F ⟶ moduleSingle R M₁} {piG : G ⟶ moduleSingle R M₂}
    [IsFreeResolution piF] [IsFreeResolution piG]
    {f : ModuleCat.of R M₁ ⟶ ModuleCat.of R M₂}
    (alpha : ProjectiveResolution.Hom (toProjectiveResolution piF)
      (toProjectiveResolution piG) f) (i : ℕ) :=
  HomologicalComplex.homologyMap (tensorComplexMap N alpha) i

/-- Lemma 10.75.1 (1) (00LZ): compatible lifts of the same module map induce the same map on
tensor-complex homology. -/
@[stacks 00LZ "(1), independence of the compatible lift after tensoring"]
theorem tensorHomologyMap_eq_of_compatibleLifts
    (N : Type u) [AddCommGroup N] [Module R N]
    (f : ModuleCat.of R M₁ ⟶ ModuleCat.of R M₂)
    (piF : F ⟶ moduleSingle R M₁) (piG : G ⟶ moduleSingle R M₂)
    [IsFreeResolution piF] [IsFreeResolution piG]
    (alpha beta : ProjectiveResolution.Hom (toProjectiveResolution piF)
      (toProjectiveResolution piG) f) (i : ℕ) :
    tensorHomologyMap N alpha i = tensorHomologyMap N beta i := sorry

/-- Lemma 10.75.1 (2) (00LZ): a lifted module isomorphism induces an isomorphism on every
tensor-complex homology group. -/
@[stacks 00LZ "(2), tensor-homology isomorphism induced by a lifted isomorphism"]
theorem tensorHomologyMap_isIso_of_isIso
    (N : Type u) [AddCommGroup N] [Module R N]
    (f : ModuleCat.of R M₁ ⟶ ModuleCat.of R M₂) [IsIso f]
    (piF : F ⟶ moduleSingle R M₁) (piG : G ⟶ moduleSingle R M₂)
    [IsFreeResolution piF] [IsFreeResolution piG]
    (alpha : ProjectiveResolution.Hom (toProjectiveResolution piF)
      (toProjectiveResolution piG) f) (i : ℕ) :
    IsIso (tensorHomologyMap N alpha i) := sorry

/-- Lemma 10.75.1 (3) (00LZ): a compatible lift of the identity induces the identity on every
tensor-complex homology group. -/
@[stacks 00LZ "(3), identity induced by an identity lift after tensoring"]
theorem tensorHomologyMap_eq_id
    (N : Type u) [AddCommGroup N] [Module R N]
    (piF : F ⟶ moduleSingle R M₁) [IsFreeResolution piF]
    (alpha : ProjectiveResolution.Hom (toProjectiveResolution piF)
      (toProjectiveResolution piF) (𝟙 (ModuleCat.of R M₁))) (i : ℕ) :
    tensorHomologyMap N alpha i = 𝟙 _ := sorry

end ChainComplex.IsFreeResolution
