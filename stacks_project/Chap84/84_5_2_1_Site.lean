module

public import Mathlib.CategoryTheory.Sites.Continuous
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap84.Lemma_84_5_2_Relocalization

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SmallToBig

/-!
# Small-to-big étale restriction of algebraic spaces

The big étale topology compatibility name and the canonical restriction API.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The big étale Grothendieck topology on algebraic spaces over `S`. -/
abbrev bigEtaleTopology {S : Scheme.{u}} : GrothendieckTopology (AlgebraicSpace S) :=
  etaleTopology

#check (etaleTopology_def : ∀ {S : Scheme.{u}},
  (etaleTopology : GrothendieckTopology (AlgebraicSpace S)) =
    (etalePrecoverage : Precoverage (AlgebraicSpace S)).toGrothendieck)

#check (overEtaleTopology_def : ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
  overEtaleTopology X = etaleTopology.over X)

#check (smallEtalePresentationUnitIso : ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
  𝟭 (Sheaf (spacesEtaleTopology X) (Type (u + 1))) ≅
    (smallEtaleToSpaces X).sheafPushforwardContinuous (Type (u + 1))
        (smallEtaleTopology X) (spacesEtaleTopology X) ⋙
      smallEtalePresentationExtension X)

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig

open AlgebraicGeometry.AlgebraicSpace

#check (smallEtaleToBig : ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    smallEtaleSite X ⥤ Over X)

#check (smallEtaleToBig_eq : ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    smallEtaleToBig X =
      smallEtaleToSpaces X ⋙ MorphismProperty.Over.forget (@Etale S) ⊤ X)

#check (smallEtaleToBig_obj_hom : ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
    (U : smallEtaleSite X),
    ((smallEtaleToBig X).obj U).hom = U.hom)

#check (spacesEtaleToBig : ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    spacesEtaleSite X ⥤ Over X)

#check (smallEtaleToBig_eq_comp : ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    smallEtaleToBig X = smallEtaleToSpaces X ⋙ spacesEtaleToBig X)

#check (spacesEtaleToBig_isContinuous : ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    (spacesEtaleToBig X).IsContinuous (spacesEtaleTopology X) (overEtaleTopology X))

#check (smallEtaleToBig_isContinuous : ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    (smallEtaleToBig X).IsContinuous (smallEtaleTopology X) (overEtaleTopology X))

#check (restrictToSmallEtale : ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    Sheaf (overEtaleTopology X) (Type (u + 1)) ⥤
      Sheaf (smallEtaleTopology X) (Type (u + 1)))

#check (restrictToSmallEtale_eq : ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    restrictToSmallEtale X =
      (smallEtaleToBig X).sheafPushforwardContinuous (Type (u + 1))
        (smallEtaleTopology X) (overEtaleTopology X))

#check (restrictToSmallEtale_obj : ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
    (F : Sheaf (overEtaleTopology X) (Type (u + 1))) (U : smallEtaleSite X),
    ((restrictToSmallEtale X).obj F).obj.obj (op U) =
      F.obj.obj (op ((smallEtaleToBig X).obj U)))

#check (restrictToSmallEtaleAbelian : ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    Sheaf (overEtaleTopology X) AddCommGrpCat.{u + 1} ⥤
      Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})

#check (restrictToSmallEtaleAbelian_eq : ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    restrictToSmallEtaleAbelian X =
      (smallEtaleToBig X).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (smallEtaleTopology X) (overEtaleTopology X))

end AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig

end
