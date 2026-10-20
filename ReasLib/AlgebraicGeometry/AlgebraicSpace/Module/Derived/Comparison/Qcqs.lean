/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import ReasLib.CategoryTheory.Functor.Equivalence.QuasiInverse.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Subspace
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.RestrictedPushforward

/-!
# Étale affine pushforward criterion for comparison on qcqs algebraic spaces

Compatibility of derived quasi-coherent pushforward along étale morphisms from
affine spaces to quasi-compact opens with the canonical comparisons implies
that comparison is an equivalence with the restricted derived coherator as
quasi-inverse.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- On a quasi-compact and absolutely quasi-separated algebraic space, compatibility
of derived quasi-coherent pushforward with the canonical comparisons for every
étale morphism from an affine space to a quasi-compact open implies that comparison
and the restricted derived coherator are quasi-inverse. -/
theorem comparison_isQuasiInverse {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (h_etalePushforward : ∀ {W : OpenSubspace X} {V : AlgebraicSpace S} (j : V ⟶ W.X)
      [Etale j] [IsQuasiCompact W.X] [IsAffine V] [QuasiCompact j] [QuasiSeparated j],
      IsIsomorphic (QCoh.Derived.pushforward j ⋙ comparison W.X)
        (comparison V ⋙ pushforwardCohomologyIn j)) :
    (comparison X).IsQuasiInverse (inclusion X ⋙ QCoh.Derived.coherator X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
