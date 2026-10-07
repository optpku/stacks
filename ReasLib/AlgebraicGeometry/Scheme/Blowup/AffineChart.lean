module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.ExceptionalDivisor
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.IdealStalk

/-!
# Affine charts of blowups

This file defines the canonical affine chart of a chosen blowup associated to an element of the
center ideal on an affine open and characterizes its points using the exceptional divisor.
-/

@[expose] public section

namespace AlgebraicGeometry

universe u

open CategoryTheory
open scoped AlgebraicGeometry nonZeroDivisors

noncomputable section

variable {X : Scheme.{u}} {I : X.IdealSheafData}

namespace Blowup

/-- The canonical open immersion of the affine blowup chart associated to a center element into
the chosen blowup. -/
noncomputable def affineChartι (π : Blowup X I) (U : X.affineOpens) (a : I.ideal U) :
    Spec (.of (affineBlowupChart (I.ideal U) a)) ⟶ π.scheme :=
  Proj.awayι (ReesAlgebra.Grading.grade (I.ideal U))
      (ReesAlgebra.Grading.degreeOne (I.ideal U) a)
      (ReesAlgebra.Grading.degreeOne_mem (I.ideal U) a) Nat.zero_lt_one ≫
    (π.preimageAffineOpenIso U).inv ≫
    (π.hom ⁻¹ᵁ (U : X.Opens)).ι

/-- The open subset of a chosen blowup covered by the affine chart associated to a center
element. -/
noncomputable def affineChartOpen (π : Blowup X I) (U : X.affineOpens) (a : I.ideal U) :
    π.scheme.Opens :=
  @Scheme.Hom.opensRange _ _ (π.affineChartι U a) (by
    dsimp only [affineChartι]
    exact @IsOpenImmersion.comp _ _ _ _ _ inferInstance
      (@IsOpenImmersion.comp _ _ _ _ _ inferInstance
        (IsOpenImmersion.ofRestrict π.scheme
          (π.hom ⁻¹ᵁ (U : X.Opens)).isOpenEmbedding)))

/-- A point over an affine open lies in the chart associated to a center element exactly when
the element maps to a nonzerodivisor generating the stalk ideal of the exceptional divisor. -/
theorem mem_affineChartOpen_iff_exceptionalDivisor_stalkIdeal_eq_span
    (π : Blowup X I) (U : X.affineOpens) (a : I.ideal U)
    (x' : π.scheme) (hxU : π.hom x' ∈ (U : Set X)) :
    x' ∈ π.affineChartOpen U a ↔
      let a_x' : π.scheme.presheaf.stalk x' :=
        (Scheme.Hom.stalkMap π.hom x').hom
          (X.presheaf.germ (U : X.Opens) (π.hom x') hxU a.1)
      a_x' ∈ nonZeroDivisors (π.scheme.presheaf.stalk x') ∧
        RingedSpace.idealSheafStalkIdeal π.exceptionalDivisor.toSubobject x' =
          Ideal.span ({a_x'} : Set (π.scheme.presheaf.stalk x')) := sorry

end Blowup

end

end AlgebraicGeometry
