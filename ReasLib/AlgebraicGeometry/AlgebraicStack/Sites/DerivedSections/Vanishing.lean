/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.AlgebraicGeometry.AffineScheme
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Sites.DerivedSections.Abelian

/-!
# Vanishing of derived sections on algebraic stacks

Vanishing of objectwise derived sections on affine objects flat over an algebraic stack
implies vanishing of derived global sections and of cohomology in every degree.
This is an instance of vanishing detection on a covering collection of objects of a site,
using the comparison with the flat-fppf site.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.GroupoidsOver CategoryTheory CategoryTheory.Limits

noncomputable section

universe u z

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
variable [UnivLE.{u + 1, z}]

/-- If an unbounded derived abelian sheaf has zero derived sections on every affine object
flat over an algebraic stack, then its derived global sections are zero. -/
theorem derivedGlobalSections_isZero_of_derivedSections_isZero_on_affine_flat
    (K : DerivedCategory (Sheaf (inheritedFppfTopology X) AddCommGrpCat.{z}))
    (h_sections :
      ∀ (x : X.total),
        IsAffine (X.p.obj x).left → isFlat X x →
          IsZero ((siteAbelianSectionsDerived (inheritedFppfTopology X) x).obj K)) :
    IsZero ((siteAbelianGlobalSectionsDerived (inheritedFppfTopology X)).obj K) :=
  sorry

/-- If an unbounded derived abelian sheaf has zero derived sections on every affine object
flat over an algebraic stack, then its global cohomology is zero in every integer degree. -/
theorem cohomology_isZero_of_derivedSections_isZero_on_affine_flat
    (K : DerivedCategory (Sheaf (inheritedFppfTopology X) AddCommGrpCat.{z}))
    (h_sections :
      ∀ (x : X.total),
        IsAffine (X.p.obj x).left → isFlat X x →
          IsZero ((siteAbelianSectionsDerived (inheritedFppfTopology X) x).obj K))
    (i : ℤ) :
    IsZero
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{z} i).obj
        ((siteAbelianGlobalSectionsDerived (inheritedFppfTopology X)).obj K)) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
