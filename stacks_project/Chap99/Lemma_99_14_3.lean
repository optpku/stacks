/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Polarized.Stack
import StacksCheckRecall

/-!
# Lemma 99.14.3

The category Polarized is a stack in groupoids over
`Spaces'_{fp, flat, proper}` with the inherited topology, and over `Sch_fppf`.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Spaces hiding p
open CategoryTheory.Limits

universe u

/- Lemma 99.14.3
Polarized proper schemes form a stack in groupoids over proper flat finitely
presented algebraic-space families and over the fppf site of schemes. -/
@[stacks 0D40] #check
  (AlgebraicGeometry.Polarized.instIsStackInGroupoids_toFpFlatProper :
    IsStack.InGroupoids
      ((pFpFlatProperGroupoids (⊤_ Scheme.{u})).inheritedTopology
        (Scheme.fppfTopology.over (⊤_ Scheme.{u})))
      AlgebraicGeometry.Polarized.toFpFlatProper)

#check (AlgebraicGeometry.Polarized.instIsStackInGroupoids :
  IsStack.InGroupoids Scheme.fppfTopology AlgebraicGeometry.Polarized.p.{u})
