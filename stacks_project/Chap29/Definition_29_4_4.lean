/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Lattice
import StacksCheckRecall

/-!
# Definition 29.4.4

Scheme-theoretic intersections and unions of closed subschemes.

@stack 0C4H
-/

@[expose] public section

universe u

/- Definition 29.4.4: For ideal sheaves `I` and `J` on a scheme `X`, their
scheme-theoretic intersection is cut out by `I ⊔ J` (equivalently `I + J`), and their
scheme-theoretic union is cut out by `I ⊓ J`. -/
@[stacks 0C4H] #check
  (AlgebraicGeometry.Scheme.schemeTheoreticIntersection :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} (I J : X.IdealSheafData),
      AlgebraicGeometry.Scheme.{u})

#check
  (AlgebraicGeometry.Scheme.schemeTheoreticIntersection_eq_subscheme_sup :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} (I J : X.IdealSheafData),
      AlgebraicGeometry.Scheme.schemeTheoreticIntersection I J = (I ⊔ J).subscheme)

#check
  (AlgebraicGeometry.Scheme.schemeTheoreticUnion :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} (I J : X.IdealSheafData),
      AlgebraicGeometry.Scheme.{u})

#check
  (AlgebraicGeometry.Scheme.schemeTheoreticUnion_eq_subscheme_inf :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} (I J : X.IdealSheafData),
      AlgebraicGeometry.Scheme.schemeTheoreticUnion I J = (I ⊓ J).subscheme)
