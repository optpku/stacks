/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Duality.Rigidity
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.DerivedQCoh
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/- 48.12.8.2: If `f : X ⟶ Y` is proper, flat, and of finite presentation over a
quasi-compact and quasi-separated scheme, then its relative dualizing complex is
canonically isomorphic to the right adjoint along the diagonal applied to the derived
tensor product of its pullbacks along the two projections `X ×[Y] X ⟶ X`. -/
@[stacks 0E2R] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.relativeDualizingComplexIso :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
      [CompactSpace Y] → [QuasiSeparatedSpace Y] → [IsProper f] → [Flat f] →
      [Scheme.Hom.FinitePresentation f] →
      (a : DerivedQCoh Y ⥤ DerivedQCoh X) →
      (c : DerivedQCoh (CategoryTheory.Limits.pullback f f) ⥤ DerivedQCoh X) →
      (pushforwardCohomologyIn f ⊣ a) →
      (pushforwardCohomologyIn (pullback.diagonal f) ⊣ c) →
      IsIsomorphic (a.obj (structureSheaf Y))
        (c.obj (tensorObj
          ((pullback (pullback.fst f f)).obj (a.obj (structureSheaf Y)))
          ((pullback (pullback.snd f f)).obj (a.obj (structureSheaf Y))))))

end AlgebraicGeometry.Scheme.DerivedQCoh
