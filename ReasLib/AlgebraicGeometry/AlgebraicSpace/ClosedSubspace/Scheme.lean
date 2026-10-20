/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points

/-!
# Closed subschemes as algebraic spaces

A closed subscheme of a scheme over a base scheme gives an algebraic space
and its canonical inclusion into the algebraic space represented by the scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The algebraic space over `S` associated to a closed subscheme of a scheme
over `S`. -/
def ofOverClosedSubscheme {S : Scheme.{u}} (U : Over S)
    (I : U.left.IdealSheafData) : AlgebraicSpace S :=
  ofOver (Over.mk (I.subschemeι ≫ U.hom))

/-- The inclusion of a closed subscheme of `U`, as a morphism of algebraic spaces
over `S`. -/
def ofOverClosedSubschemeι {S : Scheme.{u}} (U : Over S)
    (I : U.left.IdealSheafData) :
    ofOverClosedSubscheme U I ⟶ ofOver U :=
  ofOverMap (Over.homMk I.subschemeι rfl)

/-- `ofOverClosedSubscheme U I` is `ofOver` of the structure morphism of `I.subscheme`,
and `ofOverClosedSubschemeι U I` is the corresponding `ofOverMap`. -/
theorem ofOverClosedSubscheme_spec {S : Scheme.{u}} (U : Over S)
    (I : U.left.IdealSheafData) :
    ofOverClosedSubscheme U I = ofOver (Over.mk (I.subschemeι ≫ U.hom)) ∧
      ofOverClosedSubschemeι U I = ofOverMap (Over.homMk I.subschemeι rfl) :=
  ⟨rfl, rfl⟩

end AlgebraicGeometry.AlgebraicSpace
