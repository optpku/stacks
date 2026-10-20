/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Splitting
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules

universe u

open AlgebraicGeometry.ProjectiveSpace

/- Exercise 111.52.3 (1): a finite locally free module `E` on `scheme k 2` is split if and
only if `twist k 2 E n` is split. -/
@[stacks 02AY] #check
  (AlgebraicGeometry.ProjectiveSpace.isSplit_twist_iff :
    ∀ {k : Type u} [Field k] (E : (scheme k 2).Modules) [E.IsFiniteLocallyFree] (n : ℤ),
      IsSplit E ↔ IsSplit (twist k 2 E n))

/- Exercise 111.52.3 (2): if a finite locally free module `E` on `scheme k 2` is split, then
`Scheme.Hom.cohomology (toSpec k 2) (twist k 2 E n) 1` is zero for every `n`. -/
@[stacks 02AY] #check
  (AlgebraicGeometry.ProjectiveSpace.cohomology_one_isZero_of_isSplit :
    ∀ {k : Type u} [Field k] (E : (scheme k 2).Modules) [E.IsFiniteLocallyFree]
      [IsSplit E] (n : ℤ),
      IsZero (Scheme.Hom.cohomology (toSpec k 2) (twist k 2 E n) 1))

/- Exercise 111.52.3 (3): if `L 0`, `L 1`, `L 2` are linear forms, not all zero, then the
cokernel of `linearFormHom L hL` is finite locally free if and only if `LinearIndependent k L`. -/
@[stacks 02AY] #check
  (AlgebraicGeometry.ProjectiveSpace.cokernel_isFiniteLocallyFree_iff :
    ∀ {k : Type u} [Field k]
      (L : Fin (2 + 1) → MvPolynomial (Fin (2 + 1)) k)
      (hL : ∀ i, L i ∈ grading k 2 1) (h_ne : ∃ i, L i ≠ 0),
      (cokernel (linearFormHom L hL)).IsFiniteLocallyFree ↔ LinearIndependent k L)

/- Exercise 111.52.3 (4): the cokernel of `coordinateLinearFormHom k` is finite locally free. -/
@[stacks 02AY] #check
  (AlgebraicGeometry.ProjectiveSpace.coordinateLinearFormHom_cokernel_isFiniteLocallyFree :
    ∀ (k : Type u) [Field k],
      (cokernel (coordinateLinearFormHom k)).IsFiniteLocallyFree)

/- Exercise 111.52.3 (5): if `L 0`, `L 1`, `L 2` are linear forms, not all zero, and the
cokernel of `linearFormHom L hL` is finite locally free, then that cokernel is not split. -/
@[stacks 02AY] #check
  (AlgebraicGeometry.ProjectiveSpace.cokernel_not_isSplit :
    ∀ {k : Type u} [Field k]
      (L : Fin (2 + 1) → MvPolynomial (Fin (2 + 1)) k)
      (hL : ∀ i, L i ∈ grading k 2 1) (h_ne : ∃ i, L i ≠ 0)
      [(cokernel (linearFormHom L hL)).IsFiniteLocallyFree],
      ¬ IsSplit (cokernel (linearFormHom L hL)))
