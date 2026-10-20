/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Regularity
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.HyperplaneSection.Cohomology

/-!
# Regularity of hyperplane restrictions

This file relates the canonical regularity predicates on standard projective spaces across a
hyperplane section transported from a chosen projective-space model.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace

/-- The inclusion of a hyperplane transported from the zero scheme in a chosen projective-space
model to the standard ambient projective space. -/
noncomputable abbrev transportedHyperplaneInclusion
    {k : Type u} [Field k] {n : ℕ}
    (Q : ProjectiveSpaceOver (Spec (CommRingCat.of k)) n)
    (eQ : Q.scheme ≅ scheme k n) (s : Q.tautologicalSheaf.sections)
    (φ : scheme k (n - 1) ≅ Q.tautologicalZeroScheme s) :
    scheme k (n - 1) ⟶ scheme k n :=
  φ.hom ≫ Q.tautologicalZeroSchemeι s ≫ eQ.hom

/-- The pullback of a module sheaf to a hyperplane after transporting both the hyperplane and
the ambient projective space to their standard models. -/
noncomputable abbrev transportedHyperplaneRestriction
    {k : Type u} [Field k] {n : ℕ}
    (Q : ProjectiveSpaceOver (Spec (CommRingCat.of k)) n)
    (eQ : Q.scheme ≅ scheme k n) (s : Q.tautologicalSheaf.sections)
    (φ : scheme k (n - 1) ≅ Q.tautologicalZeroScheme s)
    (ℱ : (scheme k n).Modules) : (scheme k (n - 1)).Modules :=
  (Scheme.Modules.pullback (transportedHyperplaneInclusion Q eQ s φ)).obj ℱ

namespace IsMRegular

/-- Restriction to a hyperplane preserves canonical `m`-regularity when the hyperplane-section
sequence and the ambient and restricted twisting-sheaf comparisons are supplied. -/
theorem hyperplaneRestriction
    {k : Type u} [Field k] {n : ℕ} {m : ℤ}
    (ℱ : (scheme k n).Modules) [ℱ.IsCoherent]
    (𝒢 : (scheme k (n - 1)).Modules) [𝒢.IsCoherent]
    (Q : ProjectiveSpaceOver (Spec (CommRingCat.of k)) n)
    (eQ : Q.scheme ≅ scheme k n) (s : Q.tautologicalSheaf.sections)
    (hHyperplane : ProjectiveSpaceHyperplane Q (Q.tautologicalZeroSchemeι s))
    (φ : scheme k (n - 1) ≅ Q.tautologicalZeroScheme s)
    (h𝒢 : 𝒢 ≅ transportedHyperplaneRestriction Q eQ s φ ℱ)
    (hShortExact :
      hyperplaneSectionShortExactFor Q ((Scheme.Modules.pullback eQ.hom).obj ℱ) s)
    (hAmbientTwistIso : ∀ d : ℤ,
      (Scheme.Modules.pullback eQ.hom).obj (twistingSheaf k n d) ≅
        @Scheme.Modules.tensorPowerInt Q.scheme Q.tautologicalSheaf
          Q.tautologicalSheaf_isInvertible d)
    (hRestrictionTwistIso : ∀ d : ℤ,
      (Scheme.Modules.pullback (transportedHyperplaneInclusion Q eQ s φ)).obj
          (twistingSheaf k n d) ≅
        twistingSheaf k (n - 1) d)
    (hℱ : IsMRegular k n ℱ m) :
    IsMRegular k (n - 1) 𝒢 m := sorry

/-- Over an infinite field, restriction along the hyperplane cut out by a nonzero tautological
section preserves canonical `m`-regularity. -/
theorem hyperplaneRestriction_of_nonzero
    {k : Type u} [Field k] [Infinite k] {n : ℕ} (hn : 1 ≤ n) {m : ℤ}
    (ℱ : (scheme k n).Modules) [ℱ.IsCoherent]
    (𝒢 : (scheme k (n - 1)).Modules) [𝒢.IsCoherent]
    (Q : ProjectiveSpaceOver (Spec (CommRingCat.of k)) n)
    (eQ : Q.scheme ≅ scheme k n) (s : Q.tautologicalSheaf.sections)
    (hs : Q.tautologicalSheaf.unitHomEquiv.symm s ≠ 0)
    (φ : scheme k (n - 1) ≅ Q.tautologicalZeroScheme s)
    (h𝒢 : 𝒢 ≅ transportedHyperplaneRestriction Q eQ s φ ℱ)
    (hShortExact :
      hyperplaneSectionShortExactFor Q ((Scheme.Modules.pullback eQ.hom).obj ℱ) s)
    (hAmbientTwistIso : ∀ d : ℤ,
      (Scheme.Modules.pullback eQ.hom).obj (twistingSheaf k n d) ≅
        @Scheme.Modules.tensorPowerInt Q.scheme Q.tautologicalSheaf
          Q.tautologicalSheaf_isInvertible d)
    (hRestrictionTwistIso : ∀ d : ℤ,
      (Scheme.Modules.pullback (transportedHyperplaneInclusion Q eQ s φ)).obj
          (twistingSheaf k n d) ≅
        twistingSheaf k (n - 1) d)
    (hℱ : IsMRegular k n ℱ m) :
    IsMRegular k (n - 1) 𝒢 m := sorry

end IsMRegular

end AlgebraicGeometry.ProjectiveSpace
