/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Ext.Finite
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Restrict
public import ReasLib.Algebra.Module.IdealPower.Quotient
public import ReasLib.Algebra.Module.IdealPower.System.IsIso
public import ReasLib.LinearAlgebra.QuotientByIdeal.QuotientRing

import Mathlib.Tactic.CrossRefAttribute

/-!
# Ext systems over ideal-power quotients

This file owns the two explicit systems in Lemma 15.101.8 and their source-facing comparison
statements.  The higher-degree comparison is deliberately a proposition at the quotient-category
layer; no chapter-local representative or temporary instance is exposed.

@stack 0EGY
@stack 0EGZ
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Abelian
open Ideal.PowerQuotient
open IadicFiniteModuleSystem

noncomputable section

universe u v

namespace IadicFiniteModuleSystem.Ext

variable {A : Type u} [CommRing A]

/-- The system of Ext groups modulo I ^ n. -/
@[stacks 0EGY "Ext quotient system over ideal powers"]
abbrev extQuotientSystem (I : Ideal A) (M N : ModuleCat.{v} A)
    [IsNoetherianRing A] [Small.{v} A] [Module.Finite A M] [Module.Finite A N] (i : ℕ) :
  IadicFiniteModuleSystem A I :=
  fun n ↦ FGModuleCat.of (IadicFiniteModuleSystem.stageRing A I n)
    ((Ext M N i : Type v) ⧸
      (I ^ (n : ℕ) • (⊤ : Submodule A (Ext M N i : Type v))))

/-- The system of Ext groups over the reduced rings and reduced modules. -/
@[stacks 0EGY "reduced-ring Ext system over ideal powers"]
abbrev extReductionSystem (I : Ideal A) (M N : ModuleCat.{v} A)
    [IsNoetherianRing A] [Small.{v} A] [Module.Finite A M] [Module.Finite A N] (i : ℕ) :
  IadicFiniteModuleSystem A I :=
  fun n ↦ FGModuleCat.of (IadicFiniteModuleSystem.stageRing A I n)
    (Ext (Ideal.PowerQuotient.stageOver I M (n : ℕ))
      (Ideal.PowerQuotient.stageOver I N (n : ℕ)) i : Type v)

/-! ### Cross-index weak Ext comparisons -/

/-- The reduced Ext group at stage `n`, regarded as a module over the original ring. -/
@[stacks 0EGZ "reduced Ext stage over the base ring"]
abbrev reducedExtOverBase
    (I : Ideal A) (M N : ModuleCat.{v} A)
    [IsNoetherianRing A] [Small.{v} A] [Module.Finite A M] [Module.Finite A N]
    (i : ℕ) (n : ℕ+) : ModuleCat.{v} A :=
  (ModuleCat.restrictScalars
    (algebraMap A (IadicFiniteModuleSystem.stageRing A I n))).obj
      (extReductionSystem I M N i n).obj

namespace CrossIndex

/-- The `I ^ c`-part of the reduced Ext group at stage `m`. -/
@[stacks 0EGZ "ideal-power part of a reduced Ext stage"]
abbrev power
    (I : Ideal A) (M N : ModuleCat.{v} A)
    [IsNoetherianRing A] [Small.{v} A] [Module.Finite A M] [Module.Finite A N]
    (i c : ℕ) (m : ℕ+) :
    Submodule A (reducedExtOverBase I M N i m) :=
  I ^ c • ⊤

/-- The denominator cut out by `I ^ n` inside the `I ^ c`-part at stage `m`. -/
@[stacks 0EGZ "cross-index reduced Ext denominator"]
abbrev denominator
    (I : Ideal A) (M N : ModuleCat.{v} A)
    [IsNoetherianRing A] [Small.{v} A] [Module.Finite A M] [Module.Finite A N]
    (i c : ℕ) (m n : ℕ+) :
    Submodule A (power I M N i c m) :=
  (I ^ (n : ℕ) •
      (⊤ : Submodule A (reducedExtOverBase I M N i m))).comap
    (power I M N i c m).subtype

/-- For admissible indices, the cross-index denominator maps back to the ambient `I ^ n` part.
This is the source-facing bridge to the generic ideal-power submodule API. -/
@[stacks 0EGZ "cross-index denominator equals the ambient ideal-power part"]
theorem denominator_map_subtype
    (I : Ideal A) (M N : ModuleCat.{v} A)
    [IsNoetherianRing A] [Small.{v} A] [Module.Finite A M] [Module.Finite A N]
    (i c : ℕ) (m n : ℕ+) (h : c ≤ (n : ℕ)) :
    (denominator I M N i c m n).map (power I M N i c m).subtype =
      I ^ (n : ℕ) •
        (⊤ : Submodule A (reducedExtOverBase I M N i m)) := sorry

/-- The cross-index source `I ^ c E_m / I ^ n E_m`, represented without an invalid change of
base ring.  For the admissible indices below, `c ≤ n`, so the denominator is exactly the
`I ^ n`-part of `E_m`. -/
@[stacks 0EGZ "source of the weak reduced Ext comparison"]
abbrev source
    (I : Ideal A) (M N : ModuleCat.{v} A)
    [IsNoetherianRing A] [Small.{v} A] [Module.Finite A M] [Module.Finite A N]
    (i c : ℕ) (m n : ℕ+) : ModuleCat.{v} A :=
  ModuleCat.of A
    (power I M N i c m ⧸ denominator I M N i c m n)

/-- The `I ^ c`-torsion submodule of the reduced Ext group at stage `n`. -/
@[stacks 0EGZ "torsion in a reduced Ext stage"]
abbrev torsion
    (I : Ideal A) (M N : ModuleCat.{v} A)
    [IsNoetherianRing A] [Small.{v} A] [Module.Finite A M] [Module.Finite A N]
    (i c : ℕ) (n : ℕ+) :
    Submodule A (reducedExtOverBase I M N i n) :=
  Submodule.torsionBySet A (reducedExtOverBase I M N i n)
    (↑(I ^ c) : Set A)

/-- The cross-index target `E_n / E_n[I ^ c]`. -/
@[stacks 0EGZ "target of the weak reduced Ext comparison"]
abbrev target
    (I : Ideal A) (M N : ModuleCat.{v} A)
    [IsNoetherianRing A] [Small.{v} A] [Module.Finite A M] [Module.Finite A N]
    (i c : ℕ) (n : ℕ+) : ModuleCat.{v} A :=
  ModuleCat.of A
    (reducedExtOverBase I M N i n ⧸ torsion I M N i c n)

end CrossIndex

/-- An auxiliary bounded-map witness for the source-facing cross-index formulation.
The canonical owner for later reuse is the quotient-category `HomRepresentative` API.

The bounds formalize `m ≫ n ≫ 0`: `n` is at least `stageBound`, and `m` is at least
`n + gapBound`.  The comparison maps are data precisely on this admissible range, so the
structure does not require arbitrary values at irrelevant indices. -/
@[stacks 0EGZ "auxiliary cross-index maps for reduced Ext"]
structure CrossIndexComparison
    (I : Ideal A) (M N : ModuleCat.{v} A)
    [IsNoetherianRing A] [Small.{v} A] [Module.Finite A M] [Module.Finite A N]
    (i : ℕ) where
  /-- The uniform ideal-power exponent `c`. -/
  cutoff : ℕ
  /-- A lower bound after which the target stage is admissible. -/
  stageBound : ℕ
  /-- A lower bound on the gap between source and target stages. -/
  gapBound : ℕ
  /-- Admissible target stages are beyond the ideal-power exponent. -/
  cutoff_le_stageBound : cutoff ≤ stageBound
  /-- The cross-index map family on the stable range from Remark 15.101.9. -/
  map (m n : ℕ+) (_ : stageBound ≤ (n : ℕ))
      (_ : (n : ℕ) + gapBound ≤ (m : ℕ)) :
    CrossIndex.source I M N i cutoff m n ⟶
      CrossIndex.target I M N i cutoff n

namespace CrossIndexComparison

/-- Bundle an exponent, stable range, and cross-index map family into a comparison. -/
@[stacks 0EGZ "constructor for a cross-index Ext comparison"]
def ofMaps
    {I : Ideal A} {M N : ModuleCat.{v} A}
    [IsNoetherianRing A] [Small.{v} A] [Module.Finite A M] [Module.Finite A N]
    {i : ℕ} (cutoff stageBound gapBound : ℕ)
    (cutoff_le_stageBound : cutoff ≤ stageBound)
    (map : (m n : ℕ+) → stageBound ≤ (n : ℕ) →
      (n : ℕ) + gapBound ≤ (m : ℕ) →
        (CrossIndex.source I M N i cutoff m n ⟶
          CrossIndex.target I M N i cutoff n)) :
    CrossIndexComparison I M N i :=
  ⟨cutoff, stageBound, gapBound, cutoff_le_stageBound, map⟩

/-- The kernel and cokernel of every admissible cross-index map are annihilated by the same
power `I ^ cutoff`. -/
@[stacks 0EGZ "uniform kernel and cokernel bound for cross-index Ext maps"]
def HasUniformTorsionBound
    {I : Ideal A} {M N : ModuleCat.{v} A}
    [IsNoetherianRing A] [Small.{v} A] [Module.Finite A M] [Module.Finite A N]
    {i : ℕ} (D : CrossIndexComparison I M N i) : Prop :=
  ∀ (m n : ℕ+) (hn : D.stageBound ≤ (n : ℕ))
      (hmn : (n : ℕ) + D.gapBound ≤ (m : ℕ)),
    Module.IsTorsionBySet A (LinearMap.ker (D.map m n hn hmn).hom)
        (↑(I ^ D.cutoff) : Set A) ∧
      Module.IsTorsionBySet A
        (CrossIndex.target I M N i D.cutoff n ⧸
          LinearMap.range (D.map m n hn hmn).hom)
        (↑(I ^ D.cutoff) : Set A)

end CrossIndexComparison

/-- Remark 15.101.9 (0EGZ): the reduced Ext stages admit cross-index comparison maps for
`m ≫ n ≫ 0`, with uniformly `I ^ c`-torsion kernel and cokernel. -/
@[stacks 0EGZ "existence of auxiliary bounded cross-index Ext maps"]
theorem existsCrossIndexComparison
    [IsNoetherianRing A] [Small.{v} A]
    (I : Ideal A) (M N : ModuleCat.{v} A) [Module.Finite A M] [Module.Finite A N] (i : ℕ) :
    ∃ D : CrossIndexComparison I M N i, D.HasUniformTorsionBound := sorry

/-- The Ext comparison admits a raw representative whose stage maps have a uniform eventual
kernel/cokernel torsion bound.  HomRepresentative.isIso_quotientMap_iff turns this bound into
an isomorphism after quotienting by promotion. -/
@[stacks 0EGY "bounded representative of the Ext comparison"]
theorem existsComparisonRepresentative
    [IsNoetherianRing A] [Small.{v} A]
    (I : Ideal A) (M N : ModuleCat.{v} A) [Module.Finite A M] [Module.Finite A N] (i : ℕ) :
    ∃ f : HomRepresentative (extQuotientSystem I M N i) (extReductionSystem I M N i),
      HomRepresentative.HasUniformTorsionBound f := sorry

/-- Lemma 15.101.8 (0EGY): the Ext quotient system and reduced-ring Ext system define isomorphic
objects in the quotient category of finite ideal-power module systems. -/
@[stacks 0EGY "comparison of Ext systems over ideal-power quotients"]
theorem extQuotientSystem_isomorphic_extReductionSystem
    [IsNoetherianRing A] [Small.{v} A]
    (I : Ideal A) (M N : ModuleCat.{v} A) [Module.Finite A M] [Module.Finite A N] (i : ℕ) :
    IsIsomorphic
      ((IadicFiniteModuleSystem.Category.quotient A I).obj
        (extQuotientSystem I M N i))
      ((IadicFiniteModuleSystem.Category.quotient A I).obj
        (extReductionSystem I M N i)) := sorry

end IadicFiniteModuleSystem.Ext
