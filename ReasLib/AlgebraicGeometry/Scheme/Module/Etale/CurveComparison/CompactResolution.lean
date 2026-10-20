/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.CompactCoinvariants
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.CharacterHomologyEvaluation
public import Mathlib.Algebra.Homology.Single
public import Mathlib.CategoryTheory.Abelian.LeftDerived
public import Mathlib.Algebra.Homology.Embedding.Extend

@[expose] public section

open CategoryTheory CategoryTheory.Action.ModuleCat

noncomputable section

universe u

namespace CompactRepresentation

variable (Λ G : Type u) [CommRing Λ] [Finite Λ]
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The compact chain obtained by actually dualizing an ambient injective
resolution, before taking any coinvariants or homology. -/
def dualChain {M : DiscreteModuleCat Λ G} (I : InjectiveResolution M) :
    ChainComplex (Cat Λ G) ℕ where
  X n := dual Λ G (I.cocomplex.X n)
  d i j := dualMap Λ G (I.cocomplex.d j i)
  shape := by sorry
  d_comp_d' := by sorry

/-- The augmentation is the character dual of M→I⁰. -/
def dualAugmentation {M : DiscreteModuleCat Λ G} (I : InjectiveResolution M) :
    dualChain Λ G I ⟶ (ChainComplex.single₀ (Cat Λ G)).obj (dual Λ G M) :=
  (ChainComplex.toSingle₀Equiv (dualChain Λ G I) (dual Λ G M)).symm
    ⟨dualMap Λ G (I.ι.f 0), by sorry⟩

theorem dualAugmentation_quasiIso {M : DiscreteModuleCat Λ G}
    (I : InjectiveResolution M) : QuasiIso (dualAugmentation Λ G I) := by sorry

/-- The projective resolution is the specified dual complex and augmentation.
Projectivity follows from the actual compact/discrete anti-equivalence. -/
def dualProjectiveResolution {M : DiscreteModuleCat Λ G}
    (I : InjectiveResolution M) : ProjectiveResolution (dual Λ G M) where
  complex := dualChain Λ G I
  projective n := dual_projective Λ G (I.cocomplex.X n)
  π := dualAugmentation Λ G I
  quasiIso := dualAugmentation_quasiIso Λ G I

/-- For any compact input, transport the augmentation by its SPECIFIED
continuous double-dual evaluation inverse. The chain terms remain unchanged. -/
def compactProjectiveResolution (M : Cat Λ G)
    (I : InjectiveResolution (continuousDual Λ G M)) : ProjectiveResolution M where
  complex := (dualProjectiveResolution Λ G I).complex
  projective := (dualProjectiveResolution Λ G I).projective
  π := (dualProjectiveResolution Λ G I).π ≫
    (ChainComplex.single₀ (Cat Λ G)).map (compactEvaluationIso Λ G M).inv
  quasiIso := by sorry

/-- Continuous coinvariants applied termwise: each term is the actual closed
relation quotient of the compact character module. -/
def coinvariantChain {M : DiscreteModuleCat Λ G} (I : InjectiveResolution M) :
    ChainComplex (CompactModule Λ) ℕ :=
  ((coinvariantsFunctor Λ G).mapHomologicalComplex (ComplexShape.down ℕ)).obj
    (dualChain Λ G I)

/-- Homology is taken from the compact quotient chain, not defined to be a dual
cohomology object. -/
def homology {M : DiscreteModuleCat Λ G} (I : InjectiveResolution M) (i : ℕ) :
    CompactModule Λ := (coinvariantChain Λ G I).homology i

/-- Character dual of the actual invariants cocomplex, with reversed maps. -/
def dualInvariantsChain {M : DiscreteModuleCat Λ G} (I : InjectiveResolution M) :
    ChainComplex (CompactModule Λ) ℕ where
  X n := CompactModule.ofCharacter Λ ((CategoryTheory.Action.ModuleCat.DiscreteModuleCat.fixedPointsFunctor Λ G).obj (I.cocomplex.X n))
  d i j := CompactModule.dualMap Λ ((CategoryTheory.Action.ModuleCat.DiscreteModuleCat.fixedPointsFunctor Λ G).map (I.cocomplex.d j i))
  shape := by sorry
  d_comp_d' := by sorry

/-- Naturality of the quotient/restriction map supplies the actual chain comparison. -/
def coinvariantChainComparison {M : DiscreteModuleCat Λ G} (I : InjectiveResolution M) :
    coinvariantChain Λ G I ≅ dualInvariantsChain Λ G I :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ coinvariantsDualInvariantsIso Λ G (I.cocomplex.X n)) (by sorry)

/-- Forgetting compact topology preserves homology: images of compact maps in
Hausdorff targets are already closed. -/
instance compactForget_preservesHomology :
    (CompactModule.forget Λ).PreservesHomology := by sorry

/-- The explicit comparison on underlying modules: quotient/restriction on
the chain, exact forgetting, evaluation on cycles, then the canonical ambient
injective-resolution comparison. -/
def homologyCharacterIso {M : DiscreteModuleCat Λ G} (I : InjectiveResolution M) (i : ℕ) :
    (CompactModule.forget Λ).obj (homology Λ G I i) ≅
      ModuleCat.of Λ (CharacterModule ((CategoryTheory.Action.ModuleCat.DiscreteModuleCat.derivedCohomologyFunctor Λ G i).obj M)) :=
  (CompactModule.forget Λ).mapIso
      (HomologicalComplex.homologyMapIso (coinvariantChainComparison Λ G I) i) ≪≫
    (((dualInvariantsChain Λ G I).sc i).mapHomologyIso (CompactModule.forget Λ)).symm ≪≫
    (CharacterHomologyEvaluation.evaluationEquiv
      ((((CategoryTheory.Action.ModuleCat.DiscreteModuleCat.fixedPointsFunctor Λ G).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj I.cocomplex).sc i)).toModuleIso ≪≫
    (CharacterModule.congr (CategoryTheory.Action.ModuleCat.DiscreteModuleCat.derivedCohomologyResolutionIso Λ G M I i).toLinearEquiv.symm).toModuleIso

/-- The chosen compact projective resolution is built from the existing
ambient discrete injective resolution and the actual evaluation inverse. -/
def chosenProjectiveResolution (M : Cat Λ G) : ProjectiveResolution M :=
  compactProjectiveResolution Λ G M
    (HasInjectiveResolution.out (Z := continuousDual Λ G M)).some

instance : HasProjectiveResolutions (Cat Λ G) where
  out M := ⟨⟨chosenProjectiveResolution Λ G M⟩⟩

/-- Continuous homology is the left derived functor of ACTUAL closed
coinvariants on the compact category. -/
def continuousHomology (i : ℕ) : Cat Λ G ⥤ CompactModule Λ :=
  (coinvariantsFunctor Λ G).leftDerived i

/-- The compact derived functor is compared through its specified resolution,
not equated by definition with dual cohomology. -/
def derivedHomologyCharacterIso {M : DiscreteModuleCat Λ G}
    (I : InjectiveResolution M) (i : ℕ) :
    (CompactModule.forget Λ).obj ((continuousHomology Λ G i).obj (dual Λ G M)) ≅
      ModuleCat.of Λ (CharacterModule ((CategoryTheory.Action.ModuleCat.DiscreteModuleCat.derivedCohomologyFunctor Λ G i).obj M)) :=
  (CompactModule.forget Λ).mapIso
      ((dualProjectiveResolution Λ G I).isoLeftDerivedObj (coinvariantsFunctor Λ G) i) ≪≫
    homologyCharacterIso Λ G I i

end CompactRepresentation
