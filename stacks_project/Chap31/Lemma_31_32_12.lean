/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Composition
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The canonical product of two ideal sheaves. -/
def idealSheafProduct {X : Scheme.{u}} (I J : X.IdealSheafData) : X.IdealSheafData :=
  I * J

/- Lemma 31.32.12

Let `π` be the blowup of `X` in `I` and let `π'` be the blowup of `π.scheme` in
`J.comap π.hom`. Then `π'.hom ≫ π.hom` is the blowup of `X` in `I * J`.
-/
@[stacks 080A] #check
  (AlgebraicGeometry.Blowup.compIsBlowup :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} (I J : X.IdealSheafData)
      (π : AlgebraicGeometry.Blowup X I)
      (π' : AlgebraicGeometry.Blowup π.scheme (J.comap π.hom)),
      AlgebraicGeometry.IsBlowup (π'.hom ≫ π.hom) (I * J))

end AlgebraicGeometry
