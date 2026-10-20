module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicTopology.CechNerve

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped Simplicial

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The Čech nerve of a morphism of schemes `f : X ⟶ S`, regarded as a simplicial scheme. -/
abbrev simplicialScheme : SimplicialObject Scheme.{u} :=
  (Arrow.mk f).cechNerve

/-- The degree `n` of the Čech nerve of `f : X ⟶ S` is the `(n + 1)`-fold fibre product
of `X` over `S`. -/
theorem simplicialScheme_obj (n : SimplexCategoryᵒᵖ) :
    (simplicialScheme f).obj n =
      widePullback.{0} S (fun _ : Fin (n.unop.len + 1) ↦ X) (fun _ ↦ f) :=
  Arrow.cechNerve_obj (Arrow.mk f) n

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.SimplicialObject

/-- The constant simplicial scheme with value `S`. -/
abbrev constScheme (S : Scheme.{u}) : SimplicialObject Scheme.{u} :=
  (SimplicialObject.const Scheme.{u}).obj S

/-- The constant simplicial scheme evaluates to `S` in every degree. -/
theorem constScheme_obj (S : Scheme.{u}) (n : SimplexCategoryᵒᵖ) :
    (constScheme S).obj n = S := rfl

/-- The augmentation of the Čech nerve to the constant simplicial base scheme. -/
def augmentation {X S : Scheme.{u}} (f : X ⟶ S) :
    f.simplicialScheme ⟶ constScheme S :=
  (Arrow.mk f).augmentedCechNerve.hom

/-- The components of the Čech augmentation are the base projections. -/
theorem augmentation_app {X S : Scheme.{u}} (f : X ⟶ S) (n : SimplexCategoryᵒᵖ) :
    (augmentation f).app n =
      WidePullback.base (fun _ : Fin (n.unop.len + 1) ↦ f) := rfl

end AlgebraicGeometry.SimplicialObject
