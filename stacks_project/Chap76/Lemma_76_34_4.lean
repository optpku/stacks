/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiFinite.FinitePresentationFactorization
import StacksCheckRecall

/-!
# Zariski's Main Theorem, finite-presentation addendum

A quasi-finite separated morphism of algebraic spaces which is locally of finite
presentation, with quasi-compact quasi-separated target, factors as a
quasi-compact open immersion followed by a finite morphism of finite
presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom

/- Lemma 76.34.4: With notation and hypotheses as in Lemma 76.34.3, if `f` is
moreover locally of finite presentation, the factorization `X ⟶ T ⟶ Y` may be
chosen so that `j` is a quasi-compact open immersion and `π : T ⟶ Y` is finite
and of finite presentation. -/
@[stacks 0874] #check
  (AlgebraicGeometry.AlgebraicSpace.Hom.QuasiFinite.exists_openImmersion_finitePresentationFactorization :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [QuasiFinite f] [Separated f] [LocallyOfFinitePresentation f]
      [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y],
    ∃ (T : AlgebraicSpace S) (j : X ⟶ T) (π : T ⟶ Y),
      QuasiCompact j ∧ IsOpenImmersion j ∧ IsFinite π ∧
        FinitePresentation π ∧ j ≫ π = f)

end Hom

end AlgebraicGeometry.AlgebraicSpace
