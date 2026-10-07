module

public import stacks_project.Chap63.«63_4_0_2_Admissible»
public import stacks_project.Chap63.«63_4_0_2_LowerShriekPresheaf»

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- 63.4.0.2: for a locally quasi-finite morphism `f : X ⟶ Y`, an abelian sheaf
`F` on `X_étale`, and `V` in `Y_étale`, the compact-support group is
`f_p! F(V) = colim_Z H_Z(F)`, the colimit of `H_Z(F)` over locally closed
subschemes `Z ⊂ X_V` finite over `V`. -/
@[stacks 0F6M]
theorem lowerShriekPresheaf_obj {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale) :
    ((lowerShriekPresheaf f).obj F).obj (op V) =
      colimit (FiniteSupport.diagram f F V) :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
