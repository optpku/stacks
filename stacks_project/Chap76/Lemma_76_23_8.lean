/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FiniteFreeLocus
import StacksCheckRecall

/-!
# Openness of the finite-free étale locus

If `f : X ⟶ Y` is locally of finite presentation and `F` is a finitely presented
`𝒪_X`-module flat over `Y`, the locus of points at which `F` is finite free in an
étale neighbourhood is open in `Points X`, and it is stable under arbitrary base
change of `Y`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/- Lemma 76.23.8 (1): The finite-free étale locus is open. -/
@[stacks 0CZT] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.isOpen_finiteFreeEtaleLocus.{u} :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [LocallyOfFinitePresentation f] (F : X.Modules) [F.IsFinitePresentation]
      (h_flat : flatOver F f), IsOpen (finiteFreeEtaleLocus F))

/- Lemma 76.23.8 (2): Formation of the finite-free étale locus commutes with arbitrary
base change. -/
@[stacks 0CZT] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.finiteFreeEtaleLocus_baseChange_eq_preimage.{u} :
    ∀ {S : Scheme.{u}} {X Y Y' : AlgebraicSpace S} (f : X ⟶ Y)
      [LocallyOfFinitePresentation f] (F : X.Modules) [F.IsFinitePresentation]
      (h_flat : flatOver F f) (g : Y' ⟶ Y),
        finiteFreeEtaleLocus ((pullback (pullback.fst f g)).obj F) =
          Points.map (pullback.fst f g) ⁻¹' finiteFreeEtaleLocus F)

end AlgebraicGeometry.AlgebraicSpace.Modules
