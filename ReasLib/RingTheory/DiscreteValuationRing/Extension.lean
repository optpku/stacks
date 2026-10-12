/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DiscreteValuationRing.Extension.Basic
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.BaseChange
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.BaseChange.Normalization
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.BaseChange.Galois
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.BaseChange.FormalSmooth
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.BaseChange.Abhyankar
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.Ramification
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.PurelyInseparable
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.TotalRamification
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.Uniformizer
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.FieldRamification
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.Unramified
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.Tame
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.Residue
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.Finite
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.IntegralClosure
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.Kummer
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.ArtinSchreier
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.Tower
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.WeakSolution
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.WeakSolution.FiniteExtension
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.WeakSolution.NagataDescent
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.WeakSolution.Composition
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.WeakSolution.ArtinSchreier
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.WeakSolution.PurelyInseparableStep
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.WeakSolution.EssentiallyFiniteType
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.WeakSolution.WeaklyUnramifiedBaseChange
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.WeakSolution.PurelyInseparable
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.WeakSolution.RamificationElimination
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.WeakSolution.Complete
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.WeakSolution.Epp

/-!
# Discrete valuation ring extensions

The extension aggregate exposes the reusable ramification owners, including the generic total
ramification predicate used by the Chapter 15 base-change statements.

@stack 09E9
-/
