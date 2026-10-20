/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FieldExtension.Galois
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FreeQuotient.Torsor
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Finite Galois base change as a free quotient of algebraic spaces

A finite Galois extension acts freely on the field-extension base change of an
algebraic space, and the canonical projection is a free quotient morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CommRingCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FieldExtension

namespace Galois

/-- For a finite Galois extension `k'/k`, the opposite Galois group acts freely
on the field-extension base change of any algebraic space over `k`. -/
instance instIsFree {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    [FiniteDimensional k k'] [IsGalois k k']
    (X : AlgebraicSpace (Spec (CommRingCat.of k))) :
    IsFree (opAutHom k k' X) :=
  sorry

/-- For a finite Galois extension `k'/k`, the canonical projection from the
field-extension base change of an algebraic space `X` to `X` is a free quotient
morphism for the opposite Galois action. -/
instance instIsFreeQuotient {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    [FiniteDimensional k k'] [IsGalois k k']
    (X : AlgebraicSpace (Spec (CommRingCat.of k))) :
    IsFreeQuotient (opAutHom k k' X) (baseChangeSnd k k' X) :=
  sorry

end Galois

end AlgebraicGeometry.AlgebraicSpace.FieldExtension
