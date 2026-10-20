/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Depth.Int
public import ReasLib.RingTheory.MvPolynomial.FermatQuadric
public import ReasLib.RingTheory.MvPolynomial.ReduciblePlanes
import StacksCheckRecall

@[expose] public section

universe u

open scoped ENat

/- Exercise 111.12.1 (1): the depth of `ℤ` at `(30)` is `1`. -/
@[stacks 0CS1] #check (Ideal.depth_span_thirty_int :
  Ideal.depth (Ideal.span {(30 : ℤ)}) ℤ = 1)

/- Exercise 111.12.1 (2): the depth of `ℤ ⧸ (300)` at `(30)` is `0`. -/
@[stacks 0CS1] #check (Ideal.depth_span_thirty_quotient_threeHundred :
  Ideal.depth (Ideal.span {(30 : ℤ)}) (ℤ ⧸ Ideal.span {(300 : ℤ)}) = 0)

/- Exercise 111.12.1 (3): the depth of `ℤ ⧸ (7)` at `(30)` is infinite. -/
@[stacks 0CS1] #check (Ideal.depth_span_thirty_quotient_seven :
  Ideal.depth (Ideal.span {(30 : ℤ)}) (ℤ ⧸ Ideal.span {(7 : ℤ)}) = ⊤)

/- Exercise 111.12.1 (4): the affine Fermat quadric has coordinate-ideal depth `2`. -/
@[stacks 0CS1] #check (MvPolynomial.FermatQuadric.depth_irrelevant :
  ∀ (k : Type u) [Field k],
    Ideal.depth (MvPolynomial.FermatQuadric.irrelevantIdeal k)
      (MvPolynomial.FermatQuadric.Ring k) = 2)

/- Exercise 111.12.1 (5): the union of two coordinate planes has coordinate-ideal depth `1`. -/
@[stacks 0CS1] #check (MvPolynomial.ReduciblePlanes.depth_irrelevant :
  ∀ (k : Type u) [Field k],
    Ideal.depth (MvPolynomial.ReduciblePlanes.irrelevantIdeal k)
      (MvPolynomial.ReduciblePlanes.Ring k) = 1)
