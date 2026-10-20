module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Over
public import stacks_project.Chap66.Definition_66_18_1_Site
public import stacks_project.Chap99.Lemma_99_13_1_Spaces
public import stacks_project.Chap99.Situation_99_14_1
public import ReasLib.AlgebraicGeometry.Polarized.ToSpaces

/-!
# Forgetful functor from Polarized to Spaces'_{fp, flat, proper}

A polarized pair `(X ⟶ S, L)` forgets the line bundle and is viewed as an
algebraic-space family over the terminal scheme, landing in the primed
category `Spaces'_{fp, flat, proper}`.
-/

open CategoryTheory CategoryTheory.Limits

universe u

#check (AlgebraicGeometry.Polarized.toFpFlatProper :
  AlgebraicGeometry.Polarized.Obj.{u} ⥤
    AlgebraicGeometry.AlgebraicSpace.Spaces.FpFlatProperGroupoids
      (⊤_ AlgebraicGeometry.Scheme.{u}))
