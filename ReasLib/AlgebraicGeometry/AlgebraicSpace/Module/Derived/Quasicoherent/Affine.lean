/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import ReasLib.CategoryTheory.Functor.Equivalence.QuasiInverse.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Comparison

/-! # The derived coherator on affine algebraic spaces -/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- On an affine algebraic space, the unbounded derived coherator is naturally isomorphic to
derived global sections followed by the derived associated-module functor. -/
theorem QCoh.Derived.affineDerivedCoherator_isomorphic {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsAffine X] :
    IsIsomorphic (QCoh.Derived.coherator X)
      (Modules.moduleDerivedGlobalSections X ⋙ (QCoh.tensorOX X).mapDerivedCategory) :=
  sorry

/-- On an affine algebraic space, the restriction of the derived coherator is a quasi-inverse
to the canonical comparison from derived quasi-coherent modules. -/
theorem DerivedQCoh.affineCoherator_isQuasiInverse {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsAffine X] :
    (DerivedQCoh.comparison X).IsQuasiInverse
      (DerivedQCoh.inclusion X ⋙ QCoh.Derived.coherator X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace

