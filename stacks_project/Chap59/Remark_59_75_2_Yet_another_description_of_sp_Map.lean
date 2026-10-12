/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Specialization.Derived

open AlgebraicGeometry Scheme CategoryTheory CategoryTheory.Limits Opposite

universe u

@[expose] public section

noncomputable section

variable {X Y : Scheme.{u}} (morphism : X ⟶ Y)
variable [HasWeakSheafify X.smallEtaleTopology (Type u)]
variable [HasWeakSheafify Y.smallEtaleTopology (Type u)]
variable [∀ P : Y.Etaleᵒᵖ ⥤ Type u, (smallEtalePullback morphism).op.HasLeftKanExtension P]
variable (F : Sheaf Y.smallEtaleTopology (Type u))

/- Ordinary sections pullback is available independently of specialization transport. -/
#check (AlgebraicGeometry.Scheme.etaleSectionsPullback morphism F :
  etaleGlobalSections F →
    (((smallEtalePullback morphism).sheafPullback (Type u)
      Y.smallEtaleTopology X.smallEtaleTopology).obj F).obj.obj
        (op ((smallEtalePullback morphism).obj
          (MorphismProperty.Over.mk _ (𝟙 Y) inferInstance))))

variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ P : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback morphism).op.HasLeftKanExtension P]

/- The natural abelian sections pullback remains available for conditional derived transport. -/
#check (AlgebraicGeometry.Scheme.etaleAbelianSectionsPullbackNatTrans morphism :
  siteAbelianSectionsFunctor Y.smallEtaleTopology
      (MorphismProperty.Over.mk _ (𝟙 Y) inferInstance) ⟶
    Sheaf.smallEtaleInverseImage morphism AddCommGrpCat.{u} ⋙
      siteAbelianSectionsFunctor X.smallEtaleTopology
        ((smallEtalePullback morphism).obj
          (MorphismProperty.Over.mk _ (𝟙 Y) inferInstance)))

end
