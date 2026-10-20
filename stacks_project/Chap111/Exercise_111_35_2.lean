/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.TangentSpace.DottedArrowCotangent
import StacksCheckRecall

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

/- Exercise 111.35.2: dotted tangent arrows are in bijection with the
`κ(x)`-linear dual of the cotangent space of the fibre stalk. -/
@[stacks 029E] #check
  (AlgebraicGeometry.Scheme.Hom.dottedTangentArrowEquivCotangentLinearDual :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
      (h : Function.Bijective (f.residueFieldMap x).hom),
      DottedTangentArrow f x ≃
        (IsLocalRing.CotangentSpace (fiberStalkAt f x) →ₗ[X.residueField x]
          X.residueField x))

end AlgebraicGeometry.Scheme.Hom
