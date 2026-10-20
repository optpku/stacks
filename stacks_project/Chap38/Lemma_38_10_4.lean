/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Locus.Fiber
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Lemma 38.10.4: for a locally finite type morphism `f : X ⟶ S` and a finite-type
quasicoherent module `F` on `X`, the locus where `F` is flat over `S` is open in every
scheme-theoretic fibre of `f`. -/
@[stacks 05M9]
#check (AlgebraicGeometry.Scheme.Modules.isOpen_flatOverAt_fiber :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (s : S),
    IsOpen ((f.fiberι s) ⁻¹' {x : X | flatOverAt F f x}))

end AlgebraicGeometry.Scheme.Modules
