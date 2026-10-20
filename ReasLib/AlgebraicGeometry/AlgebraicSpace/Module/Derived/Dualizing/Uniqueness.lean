/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Dualizing.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Tensor

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
open CategoryTheory CategoryTheory.DerivedCategory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.IsDualizingComplex

/-- Any two dualizing complexes on a locally Noetherian algebraic space differ, up to
isomorphism in `D(𝒪_X)`, by derived tensor with an object `L` of `D(𝒪_X)` for which
fixed-right derived tensor `- ⊗^L L` is an equivalence. -/
theorem existsInvertibleTensorIso
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsLocallyNoetherian X]
    {K K' : DerivedQCoh X} (hK : IsDualizingComplex K)
    (hK' : IsDualizingComplex K') :
    ∃ L : ModuleDerived X,
      (DerivedTensor.Right.functor L).IsEquivalence ∧
        Nonempty (K'.obj ≅ DerivedTensor.Right.obj K.obj L) := sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.IsDualizingComplex
