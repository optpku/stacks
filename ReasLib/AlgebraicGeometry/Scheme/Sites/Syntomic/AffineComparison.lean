/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Syntomic.StandardAffine
public import ReasLib.CategoryTheory.Sites.SpecialCocontinuous
import ReasLib.AlgebraicGeometry.Scheme.Cover.Syntomic.StandardRefinement

/-!
# Comparison of affine and big syntomic sites

The inclusion of affine schemes over a scheme into the big slice site is special cocontinuous
for the standard affine and big syntomic topologies. Its cocontinuous direct image therefore
induces an equivalence on set-valued sheaves.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Syntomic.AffineComparison

/-- The inclusion from the standard affine syntomic site over `S` to the big syntomic site over
`S` is special cocontinuous. -/
theorem isSpecialCocontinuous (S : Scheme.{u}) :
    (Scheme.AffineOver.forget S).IsSpecialCocontinuous
      (Scheme.Syntomic.StandardAffine.topology S)
      (Scheme.syntomicOverTopology S) := sorry

/-- The affine-to-big syntomic inclusion carries its canonical special-cocontinuity instance. -/
instance inclusionIsSpecialCocontinuous (S : Scheme.{u}) :
    (Scheme.AffineOver.forget S).IsSpecialCocontinuous
      (Scheme.Syntomic.StandardAffine.topology S)
      (Scheme.syntomicOverTopology S) :=
  isSpecialCocontinuous S

/-- The cocontinuous direct image from the standard affine syntomic site to the big syntomic
site is an equivalence on set-valued sheaves. -/
noncomputable instance directImageIsEquivalence (S : Scheme.{u}) :
    ((Scheme.AffineOver.forget S).sheafPushforwardCocontinuous (Type (u + 1))
      (Scheme.Syntomic.StandardAffine.topology S)
      (Scheme.syntomicOverTopology S)).IsEquivalence :=
  CategoryTheory.Functor.IsSpecialCocontinuous.directImage_isEquivalence.{u + 1, u + 1, u, u, u + 1}
    (Scheme.AffineOver.forget S)

end AlgebraicGeometry.Scheme.Syntomic.AffineComparison
