module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import ReasLib.AlgebraicTopology.Cech.Nerve.LowDegree

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped Simplicial

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The simplicial scheme associated to a morphism of schemes `f : X ⟶ S`, as the Čech nerve of
`f`. -/
abbrev simplicialScheme : SimplicialObject Scheme.{u} :=
  (Arrow.mk f).cechNerve

/-- Degree `n` of the simplicial scheme associated to `f : X ⟶ S` is the `(n + 1)`-fold fibre
product of `X` over `S`. -/
theorem simplicialScheme_obj (n : SimplexCategoryᵒᵖ) :
    (simplicialScheme f).obj n =
      widePullback.{0} S (fun _ : Fin (n.unop.len + 1) ↦ X) (fun _ ↦ f) :=
  sorry

end AlgebraicGeometry.Scheme.Hom

