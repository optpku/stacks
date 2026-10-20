/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Closure.NonDense
import StacksCheckRecall

@[expose] public section

universe u

variable (k : Type u) [Field k]

#check
  (AlgebraicGeometry.SchemeTheoreticClosure.NonDenseExample.Variables : Type)

#check
  (AlgebraicGeometry.SchemeTheoreticClosure.NonDenseExample.x k :
    MvPolynomial
      AlgebraicGeometry.SchemeTheoreticClosure.NonDenseExample.Variables k)

#check
  (AlgebraicGeometry.SchemeTheoreticClosure.NonDenseExample.z k :
    ℕ → MvPolynomial
      AlgebraicGeometry.SchemeTheoreticClosure.NonDenseExample.Variables k)

#check
  (AlgebraicGeometry.SchemeTheoreticClosure.NonDenseExample.relationIdeal k :
    Ideal (MvPolynomial
      AlgebraicGeometry.SchemeTheoreticClosure.NonDenseExample.Variables k))

#check
  (AlgebraicGeometry.SchemeTheoreticClosure.NonDenseExample.coordinateRing k : Type u)

#check
  (AlgebraicGeometry.SchemeTheoreticClosure.NonDenseExample.xClass k :
    AlgebraicGeometry.SchemeTheoreticClosure.NonDenseExample.coordinateRing k)

#check
  (AlgebraicGeometry.SchemeTheoreticClosure.NonDenseExample.zClass k :
    ℕ → AlgebraicGeometry.SchemeTheoreticClosure.NonDenseExample.coordinateRing k)

#check
  (AlgebraicGeometry.SchemeTheoreticClosure.NonDenseExample.openIdeal k :
    Ideal (AlgebraicGeometry.SchemeTheoreticClosure.NonDenseExample.coordinateRing k))

#check
  (AlgebraicGeometry.SchemeTheoreticClosure.NonDenseExample.scheme k :
    AlgebraicGeometry.Scheme.{u})

#check
  (AlgebraicGeometry.SchemeTheoreticClosure.NonDenseExample.open k :
    (AlgebraicGeometry.SchemeTheoreticClosure.NonDenseExample.scheme k).Opens)

#check
  (AlgebraicGeometry.SchemeTheoreticClosure.NonDenseExample.open_coe_eq_compl_zeroLocus k :
    (AlgebraicGeometry.SchemeTheoreticClosure.NonDenseExample.open k :
      Set (AlgebraicGeometry.SchemeTheoreticClosure.NonDenseExample.scheme k)) =
        (PrimeSpectrum.zeroLocus
          (AlgebraicGeometry.SchemeTheoreticClosure.NonDenseExample.openIdeal k :
            Set (AlgebraicGeometry.SchemeTheoreticClosure.NonDenseExample.coordinateRing k)))ᶜ)

/- Example 29.7.2: the explicit open in the quotient affine scheme has the whole scheme as its
scheme-theoretic closure, although it is not topologically dense. -/
@[stacks 01RC] #check
  (AlgebraicGeometry.SchemeTheoreticClosure.NonDenseExample.schemeTheoreticClosure_open k :
    AlgebraicGeometry.schemeTheoreticClosure
      (AlgebraicGeometry.SchemeTheoreticClosure.NonDenseExample.open k) =
        AlgebraicGeometry.SchemeTheoreticClosure.NonDenseExample.scheme k)

#check
  (AlgebraicGeometry.SchemeTheoreticClosure.NonDenseExample.not_dense_open k :
    ¬ Dense
      (AlgebraicGeometry.SchemeTheoreticClosure.NonDenseExample.open k :
        Set (AlgebraicGeometry.SchemeTheoreticClosure.NonDenseExample.scheme k)))
