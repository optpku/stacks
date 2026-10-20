/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ZariskiSite.Affine.Cover.Big
public import ReasLib.CategoryTheory.Sites.SpecialCocontinuous

/-!
# Comparison of affine and big Zariski sites

The inclusion of affine schemes over a scheme into the big slice site is special cocontinuous
for the standard affine and big Zariski topologies. Its cocontinuous direct image therefore
induces an equivalence on set-valued sheaves.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Zariski.AffineComparison

/-- The inclusion from the standard affine Zariski site over `S` to the big Zariski site over
`S` is special cocontinuous. -/
theorem isSpecialCocontinuous (S : Scheme.{u}) :
    (Scheme.bigAffineZariskiInclusion S).IsSpecialCocontinuous
      (Scheme.bigAffineZariskiTopology S) (Scheme.bigZariskiTopology S) := sorry

/-- The affine-to-big Zariski inclusion carries its canonical special-cocontinuity instance. -/
instance inclusionIsSpecialCocontinuous (S : Scheme.{u}) :
    (Scheme.bigAffineZariskiInclusion S).IsSpecialCocontinuous
      (Scheme.bigAffineZariskiTopology S) (Scheme.bigZariskiTopology S) :=
  isSpecialCocontinuous S

/-- The cocontinuous direct image from the standard affine Zariski site to the big Zariski site
is an equivalence on set-valued sheaves. -/
noncomputable instance directImageIsEquivalence (S : Scheme.{u}) :
    ((Scheme.bigAffineZariskiInclusion S).sheafPushforwardCocontinuous (Type (u + 1))
      (Scheme.bigAffineZariskiTopology S) (Scheme.bigZariskiTopology S)).IsEquivalence :=
  CategoryTheory.Functor.IsSpecialCocontinuous.directImage_isEquivalence.{u + 1, u + 1, u, u, u + 1}
    (Scheme.bigAffineZariskiInclusion S)

end AlgebraicGeometry.Scheme.Zariski.AffineComparison
