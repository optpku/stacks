module

public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra.Augmentation
public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra.NatRestriction

/-!
# Natural-degree restrictions of augmentations

An augmentation of an integer-indexed chain DGA restricts canonically to a map from its
natural-degree complex to the target module in degree zero.  The construction is expressed
through Mathlib's universal description `ChainComplex.toSingle₀Equiv`, so projective-resolution
clients need not reconstruct the same degreewise map.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v

namespace ChainDGAlgebra.Augmentation

variable {R : Type u} [CommRing R]
variable {A : ChainDGAlgebra.{u, v} R}
variable {S : Type v} [CommRing S] [Algebra R S]

/-- The degree-zero map underlying the natural-degree restriction of an augmentation. -/
def natRestrictionDegreeZero (augmentation : ChainDGAlgebra.Augmentation A S) :
    A.natRestriction.X 0 ⟶ ModuleCat.of R S :=
  (A.natRestrictionXIso 0).hom ≫ augmentation.toChainMap.f 0 ≫
    (ChainDGAlgebra.degreeZeroIso R S).hom

/-- The incoming degree-one differential is killed by the degree-zero augmentation map. -/
theorem natRestrictionDegreeZero_d
    (augmentation : ChainDGAlgebra.Augmentation A S) :
    A.natRestriction.d 1 0 ≫ augmentation.natRestrictionDegreeZero = 0 := sorry

/-- Restrict an augmentation to natural degrees and identify its target with the canonical
single-term natural chain complex. -/
@[stacks 09PQ "infrastructure: natural-degree restriction of an augmentation"]
def natRestriction (augmentation : ChainDGAlgebra.Augmentation A S) :
    A.natRestriction ⟶
      (ChainComplex.single₀ (ModuleCat.{v} R)).obj (ModuleCat.of R S) :=
  (ChainComplex.toSingle₀Equiv A.natRestriction (ModuleCat.of R S)).symm
    ⟨augmentation.natRestrictionDegreeZero,
      augmentation.natRestrictionDegreeZero_d⟩

/-- In degree zero, the restricted augmentation is the original augmentation followed by the
canonical identifications. -/
@[simp]
theorem natRestriction_f_zero
    (augmentation : ChainDGAlgebra.Augmentation A S) :
    augmentation.natRestriction.f 0 =
      (A.natRestrictionXIso 0).hom ≫ augmentation.toChainMap.f 0 ≫
        (ChainDGAlgebra.degreeZeroIso R S).hom := sorry

/-- The restricted augmentation vanishes in every positive natural degree. -/
@[simp]
theorem natRestriction_f_succ
    (augmentation : ChainDGAlgebra.Augmentation A S) (n : ℕ) :
    augmentation.natRestriction.f (n + 1) = 0 := sorry

end ChainDGAlgebra.Augmentation
