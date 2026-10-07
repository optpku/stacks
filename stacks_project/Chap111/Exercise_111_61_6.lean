module

public import Mathlib.AlgebraicGeometry.Birational.Birational
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReasLib.AlgebraicGeometry.Surface.Rationality
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.Genus
public import ReasLib.CategoryTheory.Limits.Over.Products
import StacksCheckRecall

/-!
# Exercise 111.61.6

Over an algebraically closed field, which of four classes of surfaces contains a
rational surface: products of smooth projective curves, such products with a
positive-genus factor, degree-4 hypersurfaces in `ℙ³`, and smooth degree-4
hypersurfaces in `ℙ³`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Curve

/- Exercise 111.61.6 (1): over an algebraically closed field `k`, the class of
surfaces `S = C₁ ⨯ C₂` with `C₁` and `C₂` smooth projective curves contains a
rational surface. -/
@[stacks 0ELL] #check
  (AlgebraicGeometry.Curve.exists_isRationalOver_prod :
    ∀ {k : Type u} [Field k] [IsAlgClosed k],
      ∃ (C₁ C₂ : SchemeOverField k)
        (_ : Curve C₁) (_ : Smooth C₁.hom) (_ : Projective C₁.hom)
        (_ : Curve C₂) (_ : Smooth C₂.hom) (_ : Projective C₂.hom),
        Scheme.IsRationalOver (C₁ ⨯ C₂).hom)

/- Exercise 111.61.6 (2): over an algebraically closed field `k`, if `C₁` and `C₂`
are smooth projective curves and the genus of `C₁` is positive, then the product
`C₁ ⨯ C₂` is not rational. -/
@[stacks 0ELL] #check
  (AlgebraicGeometry.Curve.not_isRationalOver_prod_of_genus_pos :
    ∀ {k : Type u} [Field k] [IsAlgClosed k] (C₁ C₂ : SchemeOverField k)
      [Curve C₁] [Smooth C₁.hom] [Projective C₁.hom] [GeometricallyIrreducible C₁.hom]
      [Curve C₂] [Smooth C₂.hom] [Projective C₂.hom],
      0 < genus C₁ → ¬ Scheme.IsRationalOver (C₁ ⨯ C₂).hom)

end AlgebraicGeometry.Curve

namespace AlgebraicGeometry.ProjectiveSpace.Hypersurface

/- Exercise 111.61.6 (3): over an algebraically closed field `k`, the class of
hypersurfaces `S ⊂ ℙ³` of degree `4` contains a rational surface. -/
@[stacks 0ELL] #check
  (AlgebraicGeometry.ProjectiveSpace.Hypersurface.exists_isRationalOver_degreeFour :
    ∀ {k : Type u} [Field k] [IsAlgClosed k],
      ∃ (F : MvPolynomial (Fin 4) k) (hF : F ∈ ProjectiveSpace.grading k 3 4),
        F ≠ 0 ∧ Scheme.IsRationalOver (hom 3 4 F hF))

/- Exercise 111.61.6 (4): over an algebraically closed field `k`, no smooth
hypersurface `S ⊂ ℙ³` of degree `4` is rational. -/
@[stacks 0ELL] #check
  (AlgebraicGeometry.ProjectiveSpace.Hypersurface.not_isRationalOver_smooth_degreeFour :
    ∀ {k : Type u} [Field k] [IsAlgClosed k]
      (F : MvPolynomial (Fin 4) k) (hF : F ∈ ProjectiveSpace.grading k 3 4) (hF0 : F ≠ 0)
      [Smooth (hom 3 4 F hF)],
      ¬ Scheme.IsRationalOver (hom 3 4 F hF))

end AlgebraicGeometry.ProjectiveSpace.Hypersurface
