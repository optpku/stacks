module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.TangentSpace.DottedArrow
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.TangentSpace.Map

/-!
# Tangent maps on dotted arrows

This leaf records the geometric characterization of the canonical relative
tangent map in the dual-number model.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped DualNumber

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Under a bijective residue-field map, the canonical tangent map is
postcomposition of the corresponding dotted arrows by the coefficientwise
dual-number residue-field morphism. -/
theorem relativeTangentMapAt_dottedArrow {X Y S : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ S) (x : X)
    (hκ : Function.Bijective (f.residueFieldMap x).hom)
    (D : tangentSpaceAt (f ≫ g) x) :
    ((dottedTangentArrowEquiv (f ≫ g) x).symm D).val ≫ f =
      Spec.map (dualNumberResidueFieldMap f x) ≫
        ((dottedTangentArrowEquiv g (f x)).symm
          (relativeTangentMapAt f g x hκ D)).val := sorry

end AlgebraicGeometry.Scheme.Hom
