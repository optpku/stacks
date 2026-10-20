/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Thickening.Comparison
import StacksCheckRecall

open CategoryTheory

universe u₀ v₀ u₁ v₁ u₂ v₂ u₃ v₃ w

/- 08M8::statement_repair::1 — 91.9.1.1: a morphism of thickenings of ringed topoi `(f, f')` is given by the
commutative square of morphisms of ringed topoi with vertices
`(Sh(C), O)`, `(Sh(D), O')`, `(Sh(B), O_B)`, `(Sh(B'), O_{B'})`, whose horizontal
arrows are thickenings. This is assembled by `homMk`, with `upper = i`,
`left = f`, `right = f'`, `lower = t`, and `cell : TwoIso (comp i f') (comp f t)`. -/
@[stacks 08M8] #check (RingedSite.ToposHom.Thickening.homMk :
  ∀ {A : RingedSite.{u₀, v₀, w}} {B : RingedSite.{u₁, v₁, w}}
    {C : RingedSite.{u₂, v₂, w}} {D : RingedSite.{u₃, v₃, w}}
    [A.siteTopology.HasSheafCompose (forget RingCat.{w})]
    [B.siteTopology.HasSheafCompose (forget RingCat.{w})]
    [C.siteTopology.HasSheafCompose (forget RingCat.{w})]
    [D.siteTopology.HasSheafCompose (forget RingCat.{w})]
    (i : RingedSite.ToposHom A B) (f : RingedSite.ToposHom A C)
    (f' : RingedSite.ToposHom B D) (t : RingedSite.ToposHom C D)
    [RingedSite.ToposHom.IsThickening i] [RingedSite.ToposHom.IsThickening t]
    (cell : RingedSite.ToposHom.TwoIso
      (RingedSite.ToposHom.comp i f') (RingedSite.ToposHom.comp f t)),
    RingedSite.ToposHom.CommSquare A B C D)
