/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap60.Remark_60_9_3_Functoriality
public import stacks_project.Chap60.Remark_60_8_5_Functoriality_Functor
public import ReasLib.AlgebraicGeometry.DividedPowers.Scheme.Pullback
public import stacks_project.Chap60.Definition_60_9_1
public import ReasLib.AlgebraicGeometry.Scheme.Sites.StructureSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ringed
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingedSite RingedSite.Hom
open AlgebraicGeometry.Scheme.Crystalline
open AlgebraicGeometry.Scheme.Zariski.Small

noncomputable section

universe u

/-- Standing geometric data of Remark 60.24.1: a divided-power morphism over
`ℤ_(p)`, a commutative scheme square with `p` locally nilpotent, an object of
`Cris(X'/S')`, and the Lemma 60.7.4 cartesian divided-power pullback. -/
structure HigherDirectImageContext where
  p : ℕ
  [hp : Fact (Nat.Prime p)]
  S : DividedPowerScheme.{u}
  S' : DividedPowerScheme.{u}
  Tthick : DividedPowerScheme.{u}
  T'thick : DividedPowerScheme.{u}
  s : S.scheme ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p)))
  s' : S'.scheme ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p)))
  g : DividedPowerScheme.Hom S S'
  h_g_over : g.base ≫ s' = s
  iDP : DividedPowerScheme.Hom Tthick T'thick
  πT : DividedPowerScheme.Hom Tthick S
  πT' : DividedPowerScheme.Hom T'thick S'
  h_cart : DividedPowerScheme.IsPullback iDP πT πT' g
  Xsch : Scheme.{u}
  X'sch : Scheme.{u}
  x₀ : Xsch ⟶ S.ideal.subscheme
  x'₀ : X'sch ⟶ S'.ideal.subscheme
  s₀ : S.ideal.subscheme ⟶ S'.ideal.subscheme
  fSch : Xsch ⟶ X'sch
  h_comm : fSch ≫ x'₀ = x₀ ≫ s₀
  h_s₀ : s₀ ≫ S'.ideal.subschemeι = S.ideal.subschemeι ≫ g.base
  pX : ∀ U : Xsch.affineOpens, IsNilpotent (p : Γ(Xsch, U))
  pX' : ∀ U : X'sch.affineOpens, IsNilpotent (p : Γ(X'sch, U))
  T' : smallCrystallineSite S'.scheme S'.ideal S'.dividedPowers S'.compatible X'sch x'₀
  h_T'thick : T'thick.scheme = T'.obj.1.thickening
  h_πT' : πT'.base = h_T'thick ▸ T'.obj.1.thickeningToBase
  𝒪X : Sheaf (smallCrystallineTopology p S.scheme S.ideal S.dividedPowers
      S.compatible s Xsch x₀ pX) RingCat.{u}
  𝒪Y : Sheaf (smallCrystallineTopology p S'.scheme S'.ideal S'.dividedPowers
      S'.compatible s' X'sch x'₀ pX') RingCat.{u}

attribute [instance] HigherDirectImageContext.hp

namespace HigherDirectImageContext

/-- Assemble standing Remark 60.24.1 data from a divided-power morphism over
`ℤ_(p)`, a commutative scheme square with `p` locally nilpotent, an object of
`Cris(X'/S')`, and a Lemma 60.7.4 cartesian divided-power pullback. -/
def ofSquare
    (p : ℕ) [hp : Fact (Nat.Prime p)]
    (S S' Tthick T'thick : DividedPowerScheme.{u})
    (s : S.scheme ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (s' : S'.scheme ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (g : DividedPowerScheme.Hom S S') (h_g_over : g.base ≫ s' = s)
    (iDP : DividedPowerScheme.Hom Tthick T'thick)
    (πT : DividedPowerScheme.Hom Tthick S)
    (πT' : DividedPowerScheme.Hom T'thick S')
    (h_cart : DividedPowerScheme.IsPullback iDP πT πT' g)
    (Xsch X'sch : Scheme.{u})
    (x₀ : Xsch ⟶ S.ideal.subscheme) (x'₀ : X'sch ⟶ S'.ideal.subscheme)
    (s₀ : S.ideal.subscheme ⟶ S'.ideal.subscheme) (fSch : Xsch ⟶ X'sch)
    (h_comm : fSch ≫ x'₀ = x₀ ≫ s₀)
    (h_s₀ : s₀ ≫ S'.ideal.subschemeι = S.ideal.subschemeι ≫ g.base)
    (pX : ∀ U : Xsch.affineOpens, IsNilpotent (p : Γ(Xsch, U)))
    (pX' : ∀ U : X'sch.affineOpens, IsNilpotent (p : Γ(X'sch, U)))
    (T' : smallCrystallineSite S'.scheme S'.ideal S'.dividedPowers
      S'.compatible X'sch x'₀)
    (h_T'thick : T'thick.scheme = T'.obj.1.thickening)
    (h_πT' : πT'.base = h_T'thick ▸ T'.obj.1.thickeningToBase)
    (𝒪X : Sheaf (smallCrystallineTopology p S.scheme S.ideal S.dividedPowers
      S.compatible s Xsch x₀ pX) RingCat.{u})
    (𝒪Y : Sheaf (smallCrystallineTopology p S'.scheme S'.ideal S'.dividedPowers
      S'.compatible s' X'sch x'₀ pX') RingCat.{u}) :
    HigherDirectImageContext :=
  { p := p, hp := hp, S := S, S' := S', Tthick := Tthick, T'thick := T'thick,
    s := s, s' := s', g := g, h_g_over := h_g_over, iDP := iDP, πT := πT,
    πT' := πT', h_cart := h_cart, Xsch := Xsch, X'sch := X'sch, x₀ := x₀,
    x'₀ := x'₀, s₀ := s₀, fSch := fSch, h_comm := h_comm, h_s₀ := h_s₀,
    pX := pX, pX' := pX', T' := T', h_T'thick := h_T'thick, h_πT' := h_πT',
    𝒪X := 𝒪X, 𝒪Y := 𝒪Y }

variable (c : HigherDirectImageContext)

/-- The divided-power setup morphism associated to `c.g`. -/
def setupHom : DividedPowerSchemeHom c.S.ideal c.S'.ideal c.s c.s' :=
  DividedPowerSchemeHom.of c.g.base c.s₀ c.h_s₀ c.h_g_over c.g.ideal_compatible

/-- The Zariski ringed-site map `T ⟶ T'` of the Lemma 60.7.4 pullback. -/
noncomputable def zariskiHom :
    RingedSite.Hom (ringedSite c.Tthick.scheme) (ringedSite c.T'thick.scheme) :=
  ringedHom c.iDP.base

/-- The setup morphism has the given underlying scheme map. -/
theorem setupHom_base : c.setupHom.base = c.g.base := rfl

/-- The Zariski comparison is small-Zariski base change along `iDP`. -/
theorem zariskiHom_base :
    c.zariskiHom.base = Scheme.smallZariskiPullback c.iDP.base := rfl

end HigherDirectImageContext

end
