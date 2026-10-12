/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.ClosedSubset.Generation
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 36.15.4: if `X` is quasi-compact and quasi-separated and `T` is closed with
quasi-compact complement, then `D_QCoh,T(𝒪_X)` has a perfect weak generator. -/
@[stacks 0A9A] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.SupportedOn.exists_isPerfect_isWeakGenerator :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      (T : TopologicalSpace.Closeds X), IsCompact (T.compl : Set X) →
        ∃ P : AlgebraicGeometry.Scheme.DerivedQCoh.SupportedOn X T,
          AlgebraicGeometry.RingedSpace.ModuleDerived.IsPerfect P.obj.obj ∧
            CategoryTheory.IsWeakGenerator P)
