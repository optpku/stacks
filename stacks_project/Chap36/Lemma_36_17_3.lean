/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.ClosedSubset.Perfect.Compact

@[expose] public section

open CategoryTheory

universe u

/- Lemma 36.17.3: an object of `D_QCoh,T(𝒪_X)` on a quasi-compact and
quasi-separated scheme, where `T` has quasi-compact complement, is compact if and only
if its underlying derived `𝒪_X`-module is perfect. -/
@[stacks 0A9B] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.SupportedOn.isCompactObject_iff_isPerfect :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      (T : TopologicalSpace.Closeds X) (hT : IsCompact (T.compl : Set X))
      (E : AlgebraicGeometry.Scheme.DerivedQCoh.SupportedOn X T),
    IsCompactObject E ↔ AlgebraicGeometry.RingedSpace.ModuleDerived.IsPerfect E.obj.obj)
