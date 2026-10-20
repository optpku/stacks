module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ProEtaleDerived
import StacksCheckRecall

open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

variable (X : Scheme.{u})
variable [∀ F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1},
    (etaleToProEt X).op.HasLeftKanExtension F]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [HasSheafify (ProEt.topology X) AddCommGrpCat.{u + 1}]

/- Lemma 61.19.5. The canonical derived unit is invertible on bounded-below
complexes of abelian étale sheaves. -/
@[stacks 099V] #check
  (AlgebraicGeometry.Scheme.etaleToProEt_plusAdjunction_unit_app_isIso X :
    ∀ K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}),
      IsIso (etaleToProEt_derivedUnit X K))

#check
  (AlgebraicGeometry.Scheme.etaleToProEt_plusAdjunction_unit_app_single_isIso X :
    ∀ F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1},
      IsIso
        (etaleToProEt_derivedUnit X
          ((DerivedCategory.Plus.singleFunctor
              (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (0 : ℤ)).obj F)))

end
