module

import ReasLib.Algebra.Homology.ShortComplex.Biproduct
import ReasLib.AlgebraicGeometry.RingedSpace.Module.MorphismDifferentials
import Mathlib.AlgebraicGeometry.Scheme
import StacksCheckRecall

open CategoryTheory
open CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

variable {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)

/- Remark 29.32.17: after the canonical product-differentials and diagonal-conormal
identifications, the relative differential sheaf fits into the short exact sequence with
left map `(-1, 1)` and right map `(1, 1)`. -/
@[stacks 060N] #check
  (CategoryTheory.ShortComplex.biprodDifferenceSum_shortExact
      (Ω[f.toShHom]) :
    (CategoryTheory.ShortComplex.mk
      (CategoryTheory.Limits.biprod.lift
        (-𝟙 (Ω[f.toShHom])) (𝟙 (Ω[f.toShHom])))
      (CategoryTheory.Limits.biprod.desc
        (𝟙 (Ω[f.toShHom])) (𝟙 (Ω[f.toShHom])))
      (by simp [CategoryTheory.Limits.biprod.lift_desc])).ShortExact)

/- The first arrow in the displayed sequence has components `(-1, 1)`. -/
#check
  (CategoryTheory.ShortComplex.biprodDifferenceSum_f (Ω[f.toShHom]) :
    (CategoryTheory.ShortComplex.biprodDifferenceSum (Ω[f.toShHom])).f =
      CategoryTheory.Limits.biprod.lift
        (-𝟙 (Ω[f.toShHom])) (𝟙 (Ω[f.toShHom])))

/- The second arrow in the displayed sequence has components `(1, 1)`. -/
#check
  (CategoryTheory.ShortComplex.biprodDifferenceSum_g (Ω[f.toShHom]) :
    (CategoryTheory.ShortComplex.biprodDifferenceSum (Ω[f.toShHom])).g =
      CategoryTheory.Limits.biprod.desc
        (𝟙 (Ω[f.toShHom])) (𝟙 (Ω[f.toShHom])))

/- The first binary-biproduct inclusion is a section of the sum map. -/
#check
  (CategoryTheory.Limits.biprod.inl_desc
      (𝟙 (Ω[f.toShHom])) (𝟙 (Ω[f.toShHom])) :
    (CategoryTheory.Limits.biprod.inl :
        Ω[f.toShHom] ⟶ Ω[f.toShHom] ⊞ Ω[f.toShHom]) ≫
      CategoryTheory.Limits.biprod.desc
        (𝟙 (Ω[f.toShHom])) (𝟙 (Ω[f.toShHom])) =
      𝟙 (Ω[f.toShHom]))
