/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Determinant.Composition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Perturbations of determinant maps

For a two-term cochain map, a degree `0 → -1` perturbation changes the two nonzero components by
`h ∘ d` and `d ∘ h`.  This leaf keeps those source formulas explicit, derives admissibility of the
perturbed map, and records invariance of the canonical determinant map.

@stack 0FJK
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace CochainComplex.Determinant

variable {R : Type u} [CommRing R]

local notation "Cpx" => CochainComplex (ModuleCat R) ℤ

/-- A surjective two-term perturbation of an admissible cochain map is admissible. -/
@[stacks 0FJK "admissibility of a surjective two-term perturbation"]
theorem IsAdmissible.ofPerturbation {K L : Cpx}
    [K.IsStrictlyGE (-1)] [K.IsStrictlyLE 0]
    [L.IsStrictlyGE (-1)] [L.IsStrictlyLE 0]
    {a b : K ⟶ L} (ha : IsAdmissible a) (h : K.X 0 →ₗ[R] L.X (-1))
    (hNeg : (b.f (-1)).hom = (a.f (-1)).hom + h.comp (K.d (-1) 0).hom)
    (hZero : (b.f 0).hom = (a.f 0).hom + (L.d (-1) 0).hom.comp h)
    (hbNeg : Function.Surjective (b.f (-1)).hom)
    (hbZero : Function.Surjective (b.f 0).hom) :
    IsAdmissible b := sorry
-- Proof strategy: retain the supplied component surjections and perform the
-- two-term kernel diagram chase defined by `hNeg` and `hZero`.  Injectivity and
-- surjectivity of `kernelDifferential b` reduce to the corresponding properties
-- for `a`, with the residual terms cancelled by the perturbation homotopy `h`.

/-- The inverse determinant maps of two surjectively perturbed cochain maps agree. -/
theorem map_eq_of_perturbation {K L : Cpx}
    [K.IsStrictlyGE (-1)] [K.IsStrictlyLE 0]
    [L.IsStrictlyGE (-1)] [L.IsStrictlyLE 0]
    [Module.Finite R (K.X (-1))] [Module.Projective R (K.X (-1))]
    [Module.Finite R (K.X 0)] [Module.Projective R (K.X 0)]
    [Module.Finite R (L.X (-1))] [Module.Projective R (L.X (-1))]
    [Module.Finite R (L.X 0)] [Module.Projective R (L.X 0)]
    {a b : K ⟶ L} (ha : IsAdmissible a) (h : K.X 0 →ₗ[R] L.X (-1))
    (hNeg : (b.f (-1)).hom = (a.f (-1)).hom + h.comp (K.d (-1) 0).hom)
    (hZero : (b.f 0).hom = (a.f 0).hom + (L.d (-1) 0).hom.comp h)
    (hbNeg : Function.Surjective (b.f (-1)).hom)
    (hbZero : Function.Surjective (b.f 0).hom) :
    map a ha = map b (ha.ofPerturbation h hNeg hZero hbNeg hbZero) := sorry
-- Proof strategy: localize at each maximal ideal, split the two surjective rows,
-- and compare the resulting determinant maps using short-exact naturality and
-- the identity `det(1 + h ∘ d) = det(1 + d ∘ h)`.  Descend the pointwise local
-- equality to the global linear maps.

/-- Lemma 15.123.2 (0FJK): a surjective perturbation by `h : K⁰ → L⁻¹` does not change the
covariant determinant map `line K → line L`. -/
@[stacks 0FJK "Lemma 15.123.2: determinant map is invariant under a surjective perturbation"]
theorem equiv_eq_of_perturbation {K L : Cpx}
    [K.IsStrictlyGE (-1)] [K.IsStrictlyLE 0]
    [L.IsStrictlyGE (-1)] [L.IsStrictlyLE 0]
    [Module.Finite R (K.X (-1))] [Module.Projective R (K.X (-1))]
    [Module.Finite R (K.X 0)] [Module.Projective R (K.X 0)]
    [Module.Finite R (L.X (-1))] [Module.Projective R (L.X (-1))]
    [Module.Finite R (L.X 0)] [Module.Projective R (L.X 0)]
    {a b : K ⟶ L} (ha : IsAdmissible a) (h : K.X 0 →ₗ[R] L.X (-1))
    (hNeg : (b.f (-1)).hom = (a.f (-1)).hom + h.comp (K.d (-1) 0).hom)
    (hZero : (b.f 0).hom = (a.f 0).hom + (L.d (-1) 0).hom.comp h)
    (hbNeg : Function.Surjective (b.f (-1)).hom)
    (hbZero : Function.Surjective (b.f 0).hom) :
    equiv a ha = equiv b (ha.ofPerturbation h hNeg hZero hbNeg hbZero) := sorry
-- Proof strategy: apply equality of inverses to the two linear equivalences,
-- rewrite both inverse maps with `equiv_symm_toLinearMap`, and finish with
-- `map_eq_of_perturbation`.

end CochainComplex.Determinant

end
