module

public import stacks_project.Chap92.«92_7_0_2_Triple»
public import stacks_project.Chap92.«92_7_0_2_Maps»

/-!
# The three maps of ringed topoi in the cotangent triangle

The functors `u1`, `u2`, `u3` from `C_{C/B/A}` induce morphisms of ringed topoi
`g1`, `g2`, `g3` with `O_i = g_i⁻¹ O`.
-/

@[expose] public section

open CategoryTheory
open Algebra
open CommAlgCat.Over.Polynomial
open RingedSite
open RingedSite.Chaotic
open RingedSite.Cotangent.PolynomialTriple

noncomputable section

universe u

variable (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]

/-- 92.7.0.2 (1) The morphism of ringed topoi
`g1 : (Sh(C_{C/B/A}), O1) ⟶ (Sh(C_{B/A}), O)`
induced by `u1`, with `O1 = g1⁻¹ O`. -/
@[stacks 08QT]
abbrev g1 : ToposHom (ringedSite1 A B C) (Site.ringedSite A B) :=
  toBase A B C

/-- `g1` is the morphism of ringed topoi induced by `u1`. -/
theorem g1_eq_toBase : g1 A B C = toBase A B C := sorry

/-- 92.7.0.2 (2) The morphism of ringed topoi
`g2 : (Sh(C_{C/B/A}), O2) ⟶ (Sh(C_{C/A}), O)`
induced by `u2`, with `O2 = g2⁻¹ O`. -/
@[stacks 08QT]
abbrev g2 : ToposHom (ringedSite2 A B C) (Site.ringedSite A C) :=
  toOverA A B C

/-- `g2` is the morphism of ringed topoi induced by `u2`. -/
theorem g2_eq_toOverA : g2 A B C = toOverA A B C := sorry

/-- 92.7.0.2 (3) The morphism of ringed topoi
`g3 : (Sh(C_{C/B/A}), O3) ⟶ (Sh(C_{C/B}), O)`
induced by `u3`, with `O3 = g3⁻¹ O`. -/
@[stacks 08QT]
abbrev g3 : ToposHom (ringedSite3 A B C) (Site.ringedSite B C) :=
  toOverB A B C

/-- `g3` is the morphism of ringed topoi induced by `u3`. -/
theorem g3_eq_toOverB : g3 A B C = toOverB A B C := sorry
