module

public import ReasLib.AlgebraicGeometry.Group.Differentials

@[expose] public section

open CategoryTheory CategoryTheory.MonObj
open scoped AlgebraicGeometry

universe u

/- The field-freeness result is provided by the reusable invariant-differentials API. -/
#check
  (AlgebraicGeometry.Scheme.GroupDifferentials.differentials_isFree_of_field :
    ∀ {k : Type u} [Field k]
      (G : Over (AlgebraicGeometry.Spec (CommRingCat.of k))) [GrpObj G],
      SheafOfModules.IsFree Ω[G.hom.toShHom])
