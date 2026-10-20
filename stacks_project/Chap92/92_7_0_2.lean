/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap92.«92_7_0_2_Triple»
public import stacks_project.Chap92.«92_7_0_2_Maps»
public import ReasLib.AlgebraicGeometry.RingedSite.Cotangent.PolynomialTower
import StacksCheckRecall

/-!
# The three maps of ringed topoi in the cotangent triangle

The functors `u1`, `u2`, `u3` from `C_{C/B/A}` induce morphisms of ringed topoi
`g1`, `g2`, `g3` with `O_i = g_i⁻¹ O`.
-/

@[expose] public section

open CategoryTheory
open RingedSite

noncomputable section

universe u

variable (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]

/- 92.7.0.2 The three morphisms of ringed topoi induced by the polynomial-square
projections, with structure sheaves given by inverse image. -/
@[stacks 08QT] #check (RingedSite.Cotangent.PolynomialTower.toBase A B C :
  RingedSite.ToposHom (RingedSite.Cotangent.PolynomialTower.ringedSite1 A B C)
    (CommAlgCat.Over.Polynomial.Site.ringedSite A B))

#check (RingedSite.Cotangent.PolynomialTower.toOverA A B C :
  RingedSite.ToposHom (RingedSite.Cotangent.PolynomialTower.ringedSite2 A B C)
    (CommAlgCat.Over.Polynomial.Site.ringedSite A C))

#check (RingedSite.Cotangent.PolynomialTower.toOverB A B C :
  RingedSite.ToposHom (RingedSite.Cotangent.PolynomialTower.ringedSite3 A B C)
    (CommAlgCat.Over.Polynomial.Site.ringedSite B C))
