module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Units

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Etale.Small

/- The additive presheaf and sheaf of units on the small etale site. -/
#check (unitsAddPresheaf : ∀ X : Scheme.{u},
  X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u})

#check (unitsAddPresheaf_isSheaf : ∀ X : Scheme.{u},
  Presheaf.IsSheaf X.smallEtaleTopology (unitsAddPresheaf X))

#check (unitsAddSheaf : ∀ X : Scheme.{u},
  Sheaf X.smallEtaleTopology AddCommGrpCat.{u})

#check (unitsAddSheaf_obj : ∀ (X : Scheme.{u}) (U : X.Etaleᵒᵖ),
  (unitsAddSheaf X).1.obj U =
    CommGrpCat.toAddCommGrp.obj (CommGrpCat.of Γ((unop U).left, ⊤)ˣ))

end AlgebraicGeometry.Scheme.Etale.Small
