module

public import ReasLib.AlgebraicTopology.DoldKan.QInftyImage
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Degreewise evaluation of the Dold--Kan projector image

Evaluation of the chain-level image of `QInfty` agrees with the categorical image of the
corresponding degree component.  This canonical layer is independent of the source-facing
finite-supremum presentation of degenerate simplices.

@stack 019A
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Simplicial DoldKan

noncomputable section

universe v u

namespace AlgebraicTopology.DoldKan.QInfty

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [HasFiniteLimits C] [HasFiniteColimits C] [HasImages C]
variable [HasImages (ChainComplex C ℕ)] [StrongEpiCategory C]

/-- Degreewise evaluation of the canonical `QInfty` image is canonically identified with the
categorical image of the corresponding component. -/
@[stacks 019A "canonical degenerate projector degree image comparison"]
noncomputable def evalImageIso (U : SimplicialObject C) (n : ℕ) :
    (QInfty.image U).X n ≅
      Limits.image ((HomologicalComplex.eval C (ComplexShape.down ℕ) n).map
        (QInfty : K[U] ⟶ K[U])) :=
  (PreservesImage.iso (HomologicalComplex.eval C (ComplexShape.down ℕ) n)
    (QInfty : K[U] ⟶ K[U])).symm

/-- The canonical chain-level image is identified with its degreewise image subobject. -/
@[stacks 019A "canonical degenerate projector degreewise image iso"]
noncomputable def degreeIso (U : SimplicialObject C) (n : ℕ) :
    (QInfty.image U).X n ≅ (QInfty.degreeSubobject U n : C) :=
  QInfty.evalImageIso U n ≪≫
    (Limits.imageSubobjectIso ((HomologicalComplex.eval C (ComplexShape.down ℕ) n).map
      (QInfty : K[U] ⟶ K[U]))).symm

namespace degreeIso

/-- Under `degreeIso`, the canonical image inclusion is the corresponding component of
`QInfty.fromImage`. -/
@[reassoc, stacks 019A "canonical degenerate projector degree image inclusion comparison"]
theorem hom_comp_arrow (U : SimplicialObject C) (n : ℕ) :
    (QInfty.degreeIso U n).hom ≫ (QInfty.degreeSubobject U n).arrow =
      (QInfty.fromImage U).f n := sorry

/-- Under `degreeIso`, the corresponding component of `QInfty.toImage` is the canonical
degreewise image projection. -/
@[reassoc, stacks 019A "canonical degenerate projector degree image projection comparison"]
theorem toImage_f_comp_hom (U : SimplicialObject C) (n : ℕ) :
    (QInfty.toImage U).f n ≫ (QInfty.degreeIso U n).hom =
      QInfty.degreeProjection U n := sorry

/-- The canonical image inclusion is recovered from the degreewise image map through the inverse
of `degreeIso`. -/
@[reassoc, stacks 019A "canonical degenerate projector degree image inclusion via inverse"]
theorem inv_comp_fromImage_f (U : SimplicialObject C) (n : ℕ) :
    (QInfty.degreeIso U n).inv ≫ (QInfty.fromImage U).f n =
      (QInfty.degreeSubobject U n).arrow := sorry

/-- The degreewise image projection is recovered from the subobject projection through the
inverse of `degreeIso`. -/
@[reassoc, stacks 019A "canonical degenerate projector degree image projection via inverse"]
theorem degreeProjection_comp_inv (U : SimplicialObject C) (n : ℕ) :
    QInfty.degreeProjection U n ≫ (QInfty.degreeIso U n).inv =
      (QInfty.toImage U).f n := sorry

end degreeIso

end AlgebraicTopology.DoldKan.QInfty
