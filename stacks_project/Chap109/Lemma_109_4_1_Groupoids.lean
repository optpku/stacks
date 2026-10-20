module

public import stacks_project.Chap99.Lemma_99_14_8_Groupoids
public import ReasLib.AlgebraicGeometry.PolarizedCurves.Groupoids

/-!
# PolarizedCurves as a category fibred in groupoids over Spec ℤ

The forgetful functor of PolarizedCurves, composed with the identification of
`Sch_fppf` with `Sch / Spec ℤ`, is packaged as an object of `GroupoidsOver specZ`,
together with the inclusion 1-morphism into Polarized.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open FiberedCategoryOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.PolarizedCurves

#check (AlgebraicGeometry.PolarizedCurves.instIsFiberedInGroupoids_toOverSpecZ.{u} :
  Functor.IsFibered.InGroupoids (p ⋙ Polarized.schemeToOverSpecZ))

#check (AlgebraicGeometry.PolarizedCurves.toGroupoidsOverSpecZ.{u} : GroupoidsOver specZ)

#check (AlgebraicGeometry.PolarizedCurves.toGroupoidsOverSpecZ_p.{u} :
  toGroupoidsOverSpecZ.p = p ⋙ Polarized.schemeToOverSpecZ)

#check (AlgebraicGeometry.PolarizedCurves.inclusionHom.{u} :
  toGroupoidsOverSpecZ ⟶ Polarized.toGroupoidsOverSpecZ)

#check (AlgebraicGeometry.PolarizedCurves.inclusionHom_toFunctor.{u} :
  Groupoids.toFunctor inclusionHom = inclusion)

#check (AlgebraicGeometry.PolarizedCurves.inclusionHom_comm.{u} :
  Groupoids.toFunctor inclusionHom ⋙ Polarized.toGroupoidsOverSpecZ.p =
    toGroupoidsOverSpecZ.p)

end AlgebraicGeometry.PolarizedCurves
