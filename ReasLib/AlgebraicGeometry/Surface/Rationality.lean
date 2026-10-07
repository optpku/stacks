module

public import Mathlib.AlgebraicGeometry.Birational.Birational
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Hypersurface
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.Genus
public import ReasLib.CategoryTheory.Limits.Over.Products

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Curve

/-- Over an algebraically closed field, a product of two smooth projective curves can be rational. -/
theorem exists_isRationalOver_prod {k : Type u} [Field k] [IsAlgClosed k] :
    ∃ (C₁ C₂ : SchemeOverField k)
      (_ : Curve C₁) (_ : Smooth C₁.hom) (_ : Projective C₁.hom)
      (_ : Curve C₂) (_ : Smooth C₂.hom) (_ : Projective C₂.hom),
      Scheme.IsRationalOver (C₁ ⨯ C₂).hom :=
  sorry

/-- A product of smooth projective curves is not rational when the first curve has positive genus. -/
theorem not_isRationalOver_prod_of_genus_pos {k : Type u} [Field k] [IsAlgClosed k]
    (C₁ C₂ : SchemeOverField k)
    [Curve C₁] [Smooth C₁.hom] [Projective C₁.hom] [GeometricallyIrreducible C₁.hom]
    [Curve C₂] [Smooth C₂.hom] [Projective C₂.hom]
    (h_genus : 0 < genus C₁) :
    ¬ Scheme.IsRationalOver (C₁ ⨯ C₂).hom :=
  sorry

end AlgebraicGeometry.Curve

namespace AlgebraicGeometry.ProjectiveSpace.Hypersurface

/-- Over an algebraically closed field, some degree-four hypersurface in projective 3-space is rational. -/
theorem exists_isRationalOver_degreeFour {k : Type u} [Field k] [IsAlgClosed k] :
    ∃ (F : MvPolynomial (Fin 4) k) (hF : F ∈ ProjectiveSpace.grading k 3 4),
      F ≠ 0 ∧ Scheme.IsRationalOver (hom 3 4 F hF) :=
  sorry

/-- A smooth degree-four hypersurface in projective 3-space is not rational. -/
theorem not_isRationalOver_smooth_degreeFour {k : Type u} [Field k] [IsAlgClosed k]
    (F : MvPolynomial (Fin 4) k) (hF : F ∈ ProjectiveSpace.grading k 3 4) (hF0 : F ≠ 0)
    [Smooth (hom 3 4 F hF)] :
    ¬ Scheme.IsRationalOver (hom 3 4 F hF) :=
  sorry

end AlgebraicGeometry.ProjectiveSpace.Hypersurface
