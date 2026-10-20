/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.Support.Generation
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.AlgebraicSpace TopologicalSpace

universe u

/- Remark 75.16.4: if `X` is a quasi-compact and quasi-separated algebraic space over a
scheme `S` and `T ⊆ |X|` is closed with quasi-compact complement, then a perfect object of
`D_QCoh,T(𝒪_X)` which is a generator for `D_QCoh,T(𝒪_X)` is a classical generator for the
perfect objects `D_perf,T(𝒪_X)`. Existence of such a
generator is Lemma 75.15.6. -/
@[stacks 0GFD]
#check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.SupportedOn.isClassicalGeneratorOfPerfect :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
      (T : Closeds (Points X)),
      IsCompact (T.compl : Set (Points X)) →
        ∀ (G : AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.SupportedOn X (T : Set (Points X))),
          ModuleDerived.IsPerfect G.obj →
            CategoryTheory.IsWeakGenerator G →
              (fun E : AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.SupportedOn X
                  (T : Set (Points X)) ↦ ModuleDerived.IsPerfect E.obj) ≤
                (CategoryTheory.ObjectProperty.singleton G).triangEnvelope)
