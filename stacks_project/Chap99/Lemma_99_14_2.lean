/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Polarized.Groupoids
import StacksCheckRecall

/-!
# Lemma 99.14.2

The category Polarized is fibred in groupoids over
`Spaces'_{fp, flat, proper}` and over `Sch_fppf`.
-/

universe u

/- Lemma 99.14.2
Polarized is fibred in groupoids over proper flat finitely presented
algebraic-space families and over schemes. -/
@[stacks 0D3Z] #check
  (AlgebraicGeometry.Polarized.instIsFiberedInGroupoids_toFpFlatProper :
    CategoryTheory.Functor.IsFibered.InGroupoids
      AlgebraicGeometry.Polarized.toFpFlatProper.{u})

#check (AlgebraicGeometry.Polarized.instIsFiberedInGroupoids :
  CategoryTheory.Functor.IsFibered.InGroupoids AlgebraicGeometry.Polarized.p.{u})

#check (AlgebraicGeometry.Polarized.toGroupoids :
  CategoryTheory.FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u}
    AlgebraicGeometry.Scheme.{u})

#check (AlgebraicGeometry.Polarized.toGroupoids_p :
  AlgebraicGeometry.Polarized.toGroupoids.{u}.p = AlgebraicGeometry.Polarized.p.{u})
