module
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import Mathlib.Algebra.Homology.QuasiIso

@[expose] public section
open CategoryTheory
noncomputable section

namespace InjectiveTargetAugmentation
variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
variable (T : C) [Injective T] (I : InjectiveResolution T)

/-- Actual comparison with the single-object injective resolution. -/
def equivalence : HomotopyEquiv ((CochainComplex.single₀ C).obj T) I.cocomplex :=
  InjectiveResolution.homotopyEquiv (InjectiveResolution.self T) I

/-- The forward map is the specified augmentation, not a chosen quasi-isomorphism. -/
theorem hom_eq : (equivalence T I).hom = I.ι := by
  simpa [equivalence, InjectiveResolution.self] using
    InjectiveResolution.homotopyEquiv_hom_ι (InjectiveResolution.self T) I

variable (F : C ⥤ D) [F.Additive]

/-- Every additive functor preserves this homotopy equivalence. No exactness
of F, and in particular no source-projectivity for a Hom functor, is assumed. -/
def mappedEquivalence := F.mapHomotopyEquiv (equivalence T I)

theorem mapped_augmentation_quasiIso :
    QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map I.ι) := by
  rw [← hom_eq T I]
  exact (mappedEquivalence T I F).quasiIso_hom

end InjectiveTargetAugmentation
