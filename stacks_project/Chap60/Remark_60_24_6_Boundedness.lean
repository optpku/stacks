/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap60.Remark_60_24_5_Quasi_coherence
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open RingedSite RingedSite.Hom
open SheafOfModules
open AlgebraicGeometry.Scheme.Hom

noncomputable section

universe u

/-- Remark 60.24.6 (Boundedness): in the situation of Remark 60.24.1, assume
that `S ⟶ S'` is quasi-compact and quasi-separated and that `X ⟶ S₀` is of
finite type and quasi-separated. Then there exists an integer `i₀` such that
for any crystal `F` in quasi-coherent `𝒪_{X/S}`-modules we have
`R^i f_cris,* F = 0` for all `i > i₀`. In the standing square this means
that `higherDirectImageModule f F i` is a zero object of modules on
`Cris(X'/S')` for every such crystal and every `i` strictly larger than `i₀`. -/
@[stacks 07MQ]
theorem crystallineHigherDirectImage_eventually_isZero
    (c : HigherDirectImageContext.{u})
    [QuasiCompact c.g.base] [QuasiSeparated c.g.base]
    [FiniteType c.x₀] [QuasiSeparated c.x₀]
    (f : RingedSite.Hom c.sourceSite c.targetSite)
    [UnivLE.{u + 1, u}]
    [HasInjectiveResolutions (RingedSite.ModuleCat.{u} c.sourceSite)]
    [∀ U : c.sourceSite,
      HasWeakSheafify (GrothendieckTopology.over c.sourceSite.siteTopology U)
        AddCommGrpCat.{u}]
    [∀ U : c.sourceSite,
      (GrothendieckTopology.over c.sourceSite.siteTopology U).WEqualsLocallyBijective
        AddCommGrpCat.{u}]
    [∀ U : c.sourceSite,
      (GrothendieckTopology.over c.sourceSite.siteTopology U).HasSheafCompose
        (forget₂ RingCat.{u} AddCommGrpCat.{u})] :
    ∃ i₀ : ℕ, ∀ (F : RingedSite.ModuleCat.{u} c.sourceSite)
      [IsCrystalInQuasiCoherentModules F] (i : ℕ),
      i₀ < i → IsZero (higherDirectImageModule f F i) :=
  sorry

end
