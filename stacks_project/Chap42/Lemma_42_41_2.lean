module

public import ReasLib.AlgebraicGeometry.ChowGroup.Degree
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup

/- Lemma 42.41.2: The degree of a zero-cycle class on a proper scheme over a field is the
finite sum of its coefficients multiplied by the dimensions over the base field of the
global-sections algebras of the corresponding reduced point closures. -/
@[stacks 0AZ2]
#check (AlgebraicGeometry.ChowGroup.degree_chowClass_eq_finsum :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (α : CycleGroup X.left
      (X.hom.relativeDimensionFunction (fun _ : Spec (CommRingCat.of k) ↦ 0)) 0),
    degree X
        (@chowClass X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
          (X.hom.relativeDimensionFunction (fun _ : Spec (CommRingCat.of k) ↦ 0))
          inferInstance 0 α) =
      ∑ᶠ x : X.left,
        CycleGroup.toAlgebraicCycle (X.hom.relativeDimensionFunction
          (fun _ : Spec (CommRingCat.of k) ↦ 0)) 0 α x *
          (Module.finrank k
            (Scheme.Hom.globalSectionsAlg (Scheme.PointClosure.ι x ≫ X.hom)) : ℤ))

end AlgebraicGeometry.ChowGroup
