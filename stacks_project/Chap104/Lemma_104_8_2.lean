/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Sites.DerivedSections.Vanishing
import StacksCheckRecall

/-!
# Lemma 104.8.2

On an algebraic stack, if objectwise derived sections of an object of
`D(X_fppf)` vanish on affine-flat objects, then global cohomology vanishes.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open AlgebraicGeometry.GroupoidsOver CategoryTheory CategoryTheory.Limits
universe u z

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
variable [UnivLE.{u + 1, z}]

/- Lemma 104.8.2: If `X` is an algebraic stack and `K` is an object of
`D(X_fppf)` such that `RΓ(x, K) = 0` for every object `x` of `X` lying over
an affine scheme `U` with `U ⟶ X` flat, then `H^i(X, K) = 0` for every `i`. -/
@[stacks 0H14] #check
  (AlgebraicGeometry.AlgebraicStack.cohomology_isZero_of_derivedSections_isZero_on_affine_flat X :
    ∀ (K : DerivedCategory (Sheaf (inheritedFppfTopology X) AddCommGrpCat.{z})),
      (∀ (x : X.total),
        IsAffine (X.p.obj x).left → isFlat X x →
          IsZero ((siteAbelianSectionsDerived (inheritedFppfTopology X) x).obj K)) →
      ∀ (i : ℤ),
        IsZero
          ((DerivedCategory.homologyFunctor AddCommGrpCat.{z} i).obj
            ((siteAbelianGlobalSectionsDerived (inheritedFppfTopology X)).obj K)))

/- Vanishing of objectwise derived sections of `K` on affine-flat objects of
`X` implies vanishing of derived global sections `RΓ(X_fppf, K)`. -/
#check
  (AlgebraicGeometry.AlgebraicStack.derivedGlobalSections_isZero_of_derivedSections_isZero_on_affine_flat X :
    ∀ (K : DerivedCategory (Sheaf (inheritedFppfTopology X) AddCommGrpCat.{z})),
      (∀ (x : X.total),
        IsAffine (X.p.obj x).left → isFlat X x →
          IsZero ((siteAbelianSectionsDerived (inheritedFppfTopology X) x).obj K)) →
      IsZero ((siteAbelianGlobalSectionsDerived (inheritedFppfTopology X)).obj K))

end AlgebraicGeometry.AlgebraicStack
