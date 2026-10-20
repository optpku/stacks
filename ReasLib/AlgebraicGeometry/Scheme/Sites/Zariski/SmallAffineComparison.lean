/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ZariskiSite.Affine.Cover.Small
public import ReasLib.CategoryTheory.Sites.SpecialCocontinuous

/-!
# Comparison of small affine and small Zariski sites

The inclusion of affine opens of a scheme into its small Zariski site is a dense subsite for
the standard small affine and small Zariski topologies. Consequently it is special
cocontinuous and its cocontinuous direct image is an equivalence on type-valued sheaves.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Zariski.SmallAffineComparison

/-- The inclusion of affine opens of `S` into its small Zariski site is a dense subsite for the
standard small affine and small Zariski topologies. -/
theorem isDenseSubsite (S : Scheme.{u}) :
    (Scheme.smallAffineZariskiInclusion S).IsDenseSubsite
      (Scheme.smallAffineZariskiTopology S) (Scheme.smallZariskiTopology S) := sorry

/-- The small-affine-to-small-Zariski inclusion carries its canonical dense-subsite
instance. -/
instance inclusionIsDenseSubsite (S : Scheme.{u}) :
    (Scheme.smallAffineZariskiInclusion S).IsDenseSubsite
      (Scheme.smallAffineZariskiTopology S) (Scheme.smallZariskiTopology S) :=
  isDenseSubsite S

/-- The inclusion of affine opens of `S` into its small Zariski site is special cocontinuous
for the standard small affine and small Zariski topologies. -/
theorem isSpecialCocontinuous (S : Scheme.{u}) :
    (Scheme.smallAffineZariskiInclusion S).IsSpecialCocontinuous
      (Scheme.smallAffineZariskiTopology S) (Scheme.smallZariskiTopology S) :=
  CategoryTheory.Functor.IsDenseSubsite.isSpecialCocontinuous
    (Scheme.smallAffineZariskiInclusion S)

/-- The cocontinuous direct image from sheaves on affine opens of `S` to sheaves on its small
Zariski site is an equivalence for type-valued sheaves. -/
noncomputable instance directImageIsEquivalence (S : Scheme.{u}) :
    ((Scheme.smallAffineZariskiInclusion S).sheafPushforwardCocontinuous (Type u)
      (Scheme.smallAffineZariskiTopology S) (Scheme.smallZariskiTopology S)).IsEquivalence :=
  CategoryTheory.Functor.IsSpecialCocontinuous.directImage_isEquivalence
    (Scheme.smallAffineZariskiInclusion S)

end AlgebraicGeometry.Scheme.Zariski.SmallAffineComparison
