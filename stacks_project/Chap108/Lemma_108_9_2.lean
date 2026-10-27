/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Picard.Relative.Separation
import StacksCheckRecall

/-! # The quasi-compact relative Picard diagonal -/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

universe u

/- Lemma 108.9.2: the diagonal of the relative Picard functor over the base is
 a quasi-compact immersion under flatness, finite presentation, properness,
 and universal preservation of the structure sheaf. -/
@[stacks 0DMF] #check
  (AlgebraicGeometry.AlgebraicSpace.RelativePicard.isQuasiCompactImmersion_diagonal :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
      [Flat f] [FinitePresentation f] [Proper f]
      [Hom.IsIsoBaseChangeStructurePushforward f],
      IsQuasiCompactImmersionOnSchemesOver (Limits.diag (picardFunctor f).obj))

#check
  (AlgebraicGeometry.AlgebraicSpace.RelativePicard.isQuasiCompactImmersion_diagonal_of_representable :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
      [Flat f] [FinitePresentation f] [Proper f]
      [Hom.IsIsoBaseChangeStructurePushforward f] {Y : AlgebraicSpace S}
      {π : Y ⟶ B} (e : (picardFunctor f).obj ≅ yonedaOver π),
      LocallySeparated π ∧ QuasiSeparated π)
