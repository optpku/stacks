/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.ChainComplex.FreeResolution
public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra.Augmentation.NatRestriction
public import ReasLib.RingTheory.DividedPowers.Tate

/-!
# Tate resolutions as projective resolutions

This file forgets the multiplicative structure of a Tate resolution and restricts its
nonnegative integer-indexed chain complex to natural degrees.  The resulting explicit
projective resolution is the input required by Mathlib's left-derived-functor API.
-/

@[expose] public section

noncomputable section

open CategoryTheory HomologicalComplex

universe u v w

namespace TateResolution

variable {R : Type u} {T : Type w} [CommRing R] [CommRing T] [Algebra R T]
variable {J : Type v} {pi0 : MvPolynomial J R →ₐ[R] T}

/-- The natural-degree chain complex underlying a Tate resolution. -/
@[stacks 09PQ "natural-degree complex underlying a Tate resolution"]
abbrev naturalComplex (A : TateResolution.{u, v, w} pi0) :
    ChainComplex (ModuleCat.{w} R) ℕ :=
  A.algebra.toChainDGAlgebra.natRestriction

/-- Degree `n` of the natural Tate complex is canonically degree `n` of the original integer
complex. -/
@[stacks 09PQ "degreewise identification of the natural Tate complex"]
def naturalComplexXIso (A : TateResolution.{u, v, w} pi0) (n : ℕ) :
    A.naturalComplex.X n ≅ A.algebra.toChainDGAlgebra.toChainComplex.X (n : ℤ) :=
  A.algebra.toChainDGAlgebra.natRestrictionXIso n

/-- The degreewise maps of the natural-degree Tate augmentation. -/
@[stacks 09PQ "components of the natural Tate augmentation"]
abbrev naturalAugmentationComponent (A : TateResolution.{u, v, w} pi0) :
    (n : ℕ) → A.naturalComplex.X n ⟶
      ((ChainComplex.single₀ (ModuleCat.{w} R)).obj (ModuleCat.of R T)).X n :=
  fun n ↦ A.augmentation.natRestriction.f n

/-- The natural-degree Tate augmentation components commute with the chain differentials. -/
@[stacks 09PQ "chain-map law for the natural Tate augmentation"]
theorem naturalAugmentationComponent_comm (A : TateResolution.{u, v, w} pi0)
    (i j : ℕ) (hij : (ComplexShape.down ℕ).Rel i j) :
    A.naturalAugmentationComponent i ≫
        ((ChainComplex.single₀ (ModuleCat.{w} R)).obj (ModuleCat.of R T)).d i j =
      A.naturalComplex.d i j ≫ A.naturalAugmentationComponent j := sorry

/-- The augmentation of a Tate resolution, restricted to its natural-degree chain complex. -/
@[stacks 09PQ "natural-degree Tate augmentation"]
abbrev naturalAugmentation (A : TateResolution.{u, v, w} pi0) :
    A.naturalComplex ⟶
      (ChainComplex.single₀ (ModuleCat.{w} R)).obj (ModuleCat.of R T) :=
  A.augmentation.natRestriction

/-- In degree zero, the natural-degree Tate augmentation is the original augmentation followed
by the canonical identifications of the two degree-zero models. -/
@[stacks 09PQ "degree-zero formula for the natural Tate augmentation", simp]
theorem naturalAugmentation_f_zero (A : TateResolution.{u, v, w} pi0) :
    A.naturalAugmentation.f 0 =
      (A.naturalComplexXIso 0).hom ≫
        A.augmentation.toChainMap.f 0 ≫
          (ChainDGAlgebra.degreeZeroIso R T).hom ≫
            (singleObjXSelf (ComplexShape.down ℕ) 0 (ModuleCat.of R T)).inv := sorry

/-- The natural-degree Tate augmentation vanishes in every positive degree. -/
@[stacks 09PQ "positive-degree vanishing of the natural Tate augmentation", simp]
theorem naturalAugmentation_f_succ (A : TateResolution.{u, v, w} pi0) (n : ℕ) :
    A.naturalAugmentation.f (n + 1) = 0 := sorry

/-- Every term of the natural-degree complex underlying a Tate resolution is a free
`R`-module. -/
@[stacks 09PQ "termwise freeness of the natural Tate complex"]
theorem naturalComplex_isTermwiseFree (A : TateResolution.{u, v, w} pi0) :
    A.naturalComplex.IsTermwiseFree := sorry

/-- Every term of the natural-degree complex underlying a Tate resolution is projective. -/
@[stacks 09PQ "termwise projectivity of the natural Tate complex"]
theorem naturalComplex_projective (A : TateResolution.{u, v, w} pi0) (n : ℕ) :
    Projective (A.naturalComplex.X n) := sorry

/-- Restricting the quasi-isomorphic Tate augmentation to natural degrees remains a
quasi-isomorphism. -/
@[stacks 09PQ "quasi-isomorphism of the natural Tate augmentation"]
theorem naturalAugmentation_quasiIso (A : TateResolution.{u, v, w} pi0) :
    QuasiIso A.naturalAugmentation := sorry

/-- The natural-degree augmentation of a Tate resolution is canonically a free resolution. -/
@[stacks 09PQ "free-resolution instance for a Tate augmentation"]
instance naturalAugmentationIsFreeResolution (A : TateResolution.{u, v, w} pi0) :
    ChainComplex.IsFreeResolution A.naturalAugmentation := sorry

/-- The projective resolution of the underlying `R`-module supplied explicitly by a Tate
resolution. -/
@[stacks 09PQ "Tate resolution as a projective resolution"]
def toProjectiveResolution (A : TateResolution.{u, v, w} pi0) :
    ProjectiveResolution (ModuleCat.of R T) :=
  ChainComplex.IsFreeResolution.toProjectiveResolution A.naturalAugmentation

/-- The chain complex of the projective resolution underlying a Tate resolution is its
natural-degree restriction. -/
@[stacks 09PQ "complex of the Tate projective resolution", simp]
theorem toProjectiveResolution_complex (A : TateResolution.{u, v, w} pi0) :
    A.toProjectiveResolution.complex = A.naturalComplex := sorry

/-- The augmentation of the projective resolution underlying a Tate resolution is the
natural-degree Tate augmentation. -/
@[stacks 09PQ "augmentation of the Tate projective resolution", simp]
theorem toProjectiveResolution_π (A : TateResolution.{u, v, w} pi0) :
    A.toProjectiveResolution.π = A.naturalAugmentation := sorry

end TateResolution
