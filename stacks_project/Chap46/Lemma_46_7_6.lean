/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Adequacy.ExtComparison
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry

universe w u

/- Lemma 46.7.6: for an affine scheme, the inclusion of adequate module sheaves into all
module sheaves induces an isomorphism on `Ext` in every nonnegative degree. -/
@[stacks 06ZW] #check
  (SheafOfModules.Adeq.mapExtAddHom_isIso :
    ∀ (τ : StandardTopology) (A : CommRingCat.{u})
      [Abelian (RingedSite.ModuleCat.{u}
        (StandardTopology.Big.ringedSite τ (Scheme.Spec.obj (op A))))]
      [ObjectProperty.IsWeakSerreClass
        (SheafOfModules.Adeq.property (Scheme.Spec.obj (op A)) τ)]
      [HasExt.{w} (SheafOfModules.Adeq.property (Scheme.Spec.obj (op A)) τ).FullSubcategory]
      [HasExt.{w} (RingedSite.ModuleCat.{u}
        (StandardTopology.Big.ringedSite τ (Scheme.Spec.obj (op A))))]
      (ℱ 𝒢 : (SheafOfModules.Adeq.property (Scheme.Spec.obj (op A)) τ).FullSubcategory)
      (i : ℕ),
      IsIso (AddCommGrpCat.ofHom
        ((SheafOfModules.Adeq.property (Scheme.Spec.obj (op A)) τ).ι.mapExtAddHom ℱ 𝒢 i)))
