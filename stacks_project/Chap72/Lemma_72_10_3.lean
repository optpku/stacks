/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FieldExtension.Galois.FreeQuotient
import StacksCheckRecall

/-!
# Finite Galois base change as a free quotient of algebraic spaces

A finite Galois extension `k'/k` acts freely on the field-extension base change
of an algebraic space `X` over `k`, and the canonical projection exhibits `X`
as the free quotient of that base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CommRingCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FieldExtension

namespace Galois

/- Lemma 72.10.3 (1): Let `k'/k` be a finite Galois extension. Let `X` be an
algebraic space over `k`. Then the opposite Galois group `(Gal(k'/k))ᵐᵒᵖ` acts
freely on the algebraic space `baseChange k k' X`. -/
@[stacks 0B86]
#check (AlgebraicGeometry.AlgebraicSpace.FieldExtension.Galois.instIsFree :
  ∀ {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    [FiniteDimensional k k'] [IsGalois k k']
    (X : AlgebraicSpace (Spec (CommRingCat.of k))),
    IsFree (opAutHom k k' X))

/- Lemma 72.10.3 (2): Let `k'/k` be a finite Galois extension. Let `X` be an
algebraic space over `k`. Then `X` is the free quotient of `baseChange k k' X`
by `(Gal(k'/k))ᵐᵒᵖ` in the sense of Properties of Spaces, Lemma 66.34.1: the
canonical projection `baseChangeSnd k k' X` is a free quotient morphism for
`opAutHom k k' X`. -/
@[stacks 0B86]
#check (AlgebraicGeometry.AlgebraicSpace.FieldExtension.Galois.instIsFreeQuotient :
  ∀ {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    [FiniteDimensional k k'] [IsGalois k k']
    (X : AlgebraicSpace (Spec (CommRingCat.of k))),
    IsFreeQuotient (opAutHom k k' X) (baseChangeSnd k k' X))

end Galois

end AlgebraicGeometry.AlgebraicSpace.FieldExtension
