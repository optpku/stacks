module

public import ReasLib.AlgebraicGeometry.SimplicialScheme.CechNerve
public import ReasLib.AlgebraicTopology.Cech.Nerve.LowDegree

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped Simplicial

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

#check (simplicialScheme : ∀ {X S : Scheme.{u}}, (X ⟶ S) → SimplicialObject Scheme.{u})

#check (simplicialScheme_obj : ∀ {X S : Scheme.{u}} (f : X ⟶ S)
    (n : SimplexCategoryᵒᵖ), (simplicialScheme f).obj n =
      widePullback.{0} S (fun _ : Fin (n.unop.len + 1) ↦ X) (fun _ ↦ f))

end AlgebraicGeometry.Scheme.Hom
