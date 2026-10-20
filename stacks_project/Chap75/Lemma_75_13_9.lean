/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Derived.InternalHom
import StacksCheckRecall

public section

universe u

/- Lemma 75.13.9. For a scheme, étale inverse image commutes with derived sheaf internal Hom
when the source is pseudo-coherent and the target is bounded below, or the source is perfect. -/
@[stacks 08JP] #check
  (AlgebraicGeometry.Scheme.SiteRestriction.isIso_comparison :
    ∀ (X : AlgebraicGeometry.Scheme.{u})
      (E F : RingedSite.Hom.ModuleDerived.{u + 1}
        (AlgebraicGeometry.Scheme.AssociatedModule.smallCommRingedSite .zariski X)),
      (E.IsPseudoCoherent ∧
        ((DerivedCategory.TStructure.t).plus : CategoryTheory.ObjectProperty _) F) ∨
          E.IsPerfect →
      CategoryTheory.IsIso (AlgebraicGeometry.Scheme.SiteRestriction.comparison X E F))

