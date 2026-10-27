/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap60.Remark_60_24_1_Higher_direct_images_Context
public import stacks_project.Chap60.Definition_60_11_3_Crystal
public import ReasLib.AlgebraicGeometry.RingedSite.Module.HigherDirectImage
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Localization
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import ReasLib.AlgebraicGeometry.Crystalline.HigherDirectImage
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open RingedSite RingedSite.Hom
open AlgebraicGeometry.Scheme.Crystalline
open SheafOfModules

noncomputable section

universe u

/-- The source crystalline ringed site of a Remark 60.24.1 square. -/
abbrev HigherDirectImageContext.sourceSite (c : HigherDirectImageContext.{u}) :=
  RingedSite.ofRingSheaf
    (smallCrystallineTopology c.p c.S.scheme c.S.ideal c.S.dividedPowers
      c.S.compatible c.s c.Xsch c.x₀ c.pX) c.𝒪X

/-- The target crystalline ringed site of a Remark 60.24.1 square. -/
abbrev HigherDirectImageContext.targetSite (c : HigherDirectImageContext.{u}) :=
  RingedSite.ofRingSheaf
    (smallCrystallineTopology c.p c.S'.scheme c.S'.ideal c.S'.dividedPowers
      c.S'.compatible c.s' c.X'sch c.x'₀ c.pX') c.𝒪Y

/- Remark 60.24.5 (Quasi-coherence): in the situation of Remark 60.24.1, assume
that `S ⟶ S'` and `X ⟶ S₀` are quasi-compact and quasi-separated. Then for a
crystal `F` in quasi-coherent `𝒪_{X/S}`-modules the sheaves `R^i f_cris,* F` are
locally quasi-coherent. In the standing square this means that the restriction of
`higherDirectImageModule f F i` to the object `(U', T', δ')` of `Cris(X'/S')` is a
quasi-coherent `𝒪_{T'}`-module, in the objectwise sense of Definition 60.11.1.
Hints: it suffices to treat affine `T'`; formula 60.24.1.1, quasi-compactness and
quasi-separatedness of `T ⟶ T'`, and Cohomology of Schemes, Lemma 30.4.5 reduce
the claim to quasi-coherence of `R^i τ_{U/T,*} F_U`. Schemes, Lemma 26.21.14
gives that `U ⟶ T₀` is quasi-compact and quasi-separated, so one may assume `p`
is locally nilpotent on `S` and work with the structure morphism `τ_{X/S}` of
Remark 60.9.6. Lemma 60.9.5 and Mayer–Vietoris (Remark 60.24.2) reduce further to
affine `X` and `S` as in Situation 60.5.1, where Propositions 60.17.4 and 60.21.3
identify crystalline cohomology with `M ⊗_D Ω_D^*`, which is compatible with
principal localization on `S` because localization of modules is exact. -/
@[stacks 07MP] #check (crystallineHigherDirectImage_isLocallyQuasiCoherent :
  ∀ {p : ℕ} [Fact p.Prime] (B B' : Base.{u} p)
    (g : DividedPowerScheme.Hom B.dividedPowerScheme B'.dividedPowerScheme)
    (hbase : g.base ≫ B'.toSpec = B.toSpec)
    (f : B.source ⟶ B'.source)
    (hf : f ≫ B'.sourceToClosed = B.sourceToClosed ≫ g.zeroFiberMap)
    [QuasiCompact g.base] [QuasiSeparated g.base]
    [QuasiCompact B.sourceToClosed] [QuasiSeparated B.sourceToClosed]
    (F : RingedSite.ModuleCat.{u + 1} B.ringedSite)
    [IsCrystalInQuasiCoherentModules F] (i : ℕ),
    ∀ A' : B'.ringedSite,
      ((Evaluation.moduleRestriction B' A').obj
        (RingedSite.ToposHom.higherDirectImageModule.{u + 1, u, u + 1, u, u + 1}
          (Ringed.morphism B B' g hbase f hf) F i)).IsQuasicoherent)

end
