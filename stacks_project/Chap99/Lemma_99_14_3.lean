/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.CategoryTheory.Fibered.InheritedTopology
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoids
public import stacks_project.Chap99.Lemma_99_14_2

/-!
# Lemma 99.14.3

The category Polarized is a stack in groupoids over
`Spaces'_{fp, flat, proper}` with the inherited topology, and over `Sch_fppf`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Spaces hiding p
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Polarized

/-- Lemma 99.14.3 (1): Polarized is a stack in groupoids over
`Spaces'_{fp, flat, proper}` via the forgetful functor `toFpFlatProper`, where
the base is endowed with the inherited topology of Definition 8.10.2. -/
@[stacks 0D40]
instance instIsStackInGroupoids_toFpFlatProper :
    IsStack.InGroupoids
      ((pFpFlatProperGroupoids (⊤_ Scheme.{u})).inheritedTopology
        (Scheme.fppfTopology.over (⊤_ Scheme.{u})))
      toFpFlatProper :=
  sorry

/-- Lemma 99.14.3 (2): Polarized is a stack in groupoids over `Sch_fppf` via the
forgetful functor `p`. -/
@[stacks 0D40]
instance instIsStackInGroupoids : IsStack.InGroupoids Scheme.fppfTopology p :=
  sorry

/-- The forgetful functor `toFpFlatProper` is a stack on the inherited topology
of `Spaces'_{fp, flat, proper}`. -/
theorem toFpFlatProper_isStackOnSite :
    IsStack.OnSite
      ((pFpFlatProperGroupoids (⊤_ Scheme.{u})).inheritedTopology
        (Scheme.fppfTopology.over (⊤_ Scheme.{u})))
      toFpFlatProper :=
  sorry

/-- The forgetful functor `p` is a stack on the site `Sch_fppf`. -/
theorem p_isStackOnSite : IsStack.OnSite Scheme.fppfTopology p :=
  sorry

end AlgebraicGeometry.Polarized
