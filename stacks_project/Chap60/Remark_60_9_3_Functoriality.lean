/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Crystalline.RingedMorphism
public import ReasLib.AlgebraicGeometry.Crystalline.Functoriality.Small

open CategoryTheory AlgebraicGeometry

universe u

variable {p : ℕ} [Fact p.Prime]
variable (B B' : AlgebraicGeometry.Scheme.Crystalline.Base.{u} p)
variable (g : DividedPowerScheme.Hom B.dividedPowerScheme B'.dividedPowerScheme)
variable (hbase : g.base ≫ B'.toSpec = B.toSpec)
variable (f : B.source ⟶ B'.source)
variable (hf : f ≫ B'.sourceToClosed = B.sourceToClosed ≫ g.zeroFiberMap)

/- Remark 60.9.3 (Functoriality)
A morphism of divided-power schemes over the prime-local integers and a
commuting source square induce the small crystalline ringed-topos morphism.
Its underlying geometric morphism is π_Y ∘ f_CRIS ∘ i_X: the inclusion at X,
the forward big crystalline morphism, and the projection at Y. -/
@[stacks 07IK] #check (AlgebraicGeometry.Scheme.Crystalline.Ringed.morphism
    B B' g hbase f hf : RingedSite.ToposHom B.ringedSite B'.ringedSite)
