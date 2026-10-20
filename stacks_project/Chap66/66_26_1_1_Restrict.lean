/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.PresentationRestriction

/-! Compatibility checks for actual étale restriction on module sheaves. -/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Sheaf.InternalModule

#check
  (AlgebraicGeometry.AlgebraicSpace.Modules.restrictFunctor :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f],
      Y.Modules ⥤ X.Modules)

#check
  (AlgebraicGeometry.AlgebraicSpace.Modules.restrictFunctorIsoPullback :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f],
      Modules.restrictFunctor f ≅ Modules.pullback f)

#check
  (AlgebraicGeometry.AlgebraicSpace.Modules.restrictFunctorIsoInverseImage :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f],
      Modules.restrictFunctor f ⋙ ToInternal.underlying (structureSheaf X) ≅
        ToInternal.underlying (structureSheaf Y) ⋙ etaleRestrictionSheaf f (Type u))
