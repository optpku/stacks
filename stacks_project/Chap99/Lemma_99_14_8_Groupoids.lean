/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Bicategory
public import stacks_project.Chap94.Definition_94_12_1_Representable
public import stacks_project.Chap99.Lemma_99_14_2
public import stacks_project.Chap99.Remark_99_14_5
public import ReasLib.AlgebraicGeometry.Polarized.Groupoids

/-!
# Polarized as a category fibred in groupoids over Spec ℤ

The forgetful functor of Polarized, composed with the identification of
`Sch_fppf` with `Sch / Spec ℤ`, is packaged as an object of `GroupoidsOver specZ`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Polarized

#check (AlgebraicGeometry.Polarized.instIsFiberedInGroupoids_toOverSpecZ.{u} :
  Functor.IsFibered.InGroupoids (p ⋙ toOverSpecZ))

#check (AlgebraicGeometry.Polarized.toGroupoidsOverSpecZ.{u} : GroupoidsOver specZ)

#check (AlgebraicGeometry.Polarized.toGroupoidsOverSpecZ_p.{u} :
  toGroupoidsOverSpecZ.p = p ⋙ toOverSpecZ)

end AlgebraicGeometry.Polarized

