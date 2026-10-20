/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.FinitePresentation.FlatOverAt
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Lemma 38.10.9: if `F` is a finite-type quasicoherent module that is flat at `x`
over a locally finitely presented morphism, then its stalk at `x` is finitely presented
over the local ring of `X` at `x`. -/
@[stacks 05I7]
#check (AlgebraicGeometry.Scheme.Modules.stalkFinitePresentationOfFlatOverAt :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (x : X), flatOverAt F f x →
      Module.FinitePresentation (X.presheaf.stalk x)
        (RingedSpace.stalkModuleCat F x))

end AlgebraicGeometry.Scheme.Modules
