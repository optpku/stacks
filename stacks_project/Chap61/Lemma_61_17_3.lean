module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.CohomologyComparison
import StacksCheckRecall

/-!
# Lemma 61.17.3

Cohomology comparisons between the big and small pro-étale sites.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ProEt

/- Lemma 61.17.3 (1): comparison of big and small pro-étale cohomology. -/
@[stacks 0F69] #check (AlgebraicGeometry.Scheme.ProEt.proetaleCohomology_piInverseImage :
  ∀ (S : Scheme.{u}) (n : ℤ)
    [HasSheafify (topology S) AddCommGrpCat.{u + 1}]
    [HasSheafify (proetaleTopology.over S) AddCommGrpCat.{u + 1}]
    [IsGrothendieckAbelian (Sheaf (topology S) AddCommGrpCat.{u + 1})]
    [IsGrothendieckAbelian (Sheaf (proetaleTopology.over S) AddCommGrpCat.{u + 1})]
    [∀ P : S.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (ProEt.forget S).op.HasLeftKanExtension P]
    (K : DerivedCategory (Sheaf (topology S) AddCommGrpCat.{u + 1})),
    IsIsomorphic
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
        ((siteAbelianSectionsDerived (proetaleTopology.over S) (Over.mk (𝟙 S))).obj
          ((piExact S).mapDerivedCategory.obj K)))
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
        ((siteAbelianSectionsDerived (topology S) (globalProEt S)).obj K)))

/- Lemma 61.17.3 (2): comparison of big and small pro-étale cohomology. -/
@[stacks 0F69] #check (AlgebraicGeometry.Scheme.ProEt.proetaleCohomology_smallInverseImage :
  ∀ {S T : Scheme.{u}} (f : T ⟶ S) (n : ℤ)
    [HasSheafify (topology S) AddCommGrpCat.{u + 1}]
    [HasSheafify (topology T) AddCommGrpCat.{u + 1}]
    [HasSheafify (proetaleTopology.over S) AddCommGrpCat.{u + 1}]
    [IsGrothendieckAbelian (Sheaf (topology S) AddCommGrpCat.{u + 1})]
    [IsGrothendieckAbelian (Sheaf (topology T) AddCommGrpCat.{u + 1})]
    [IsGrothendieckAbelian (Sheaf (proetaleTopology.over S) AddCommGrpCat.{u + 1})]
    [∀ P : S.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (ProEt.forget S).op.HasLeftKanExtension P]
    [∀ P : S.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (smallProetalePullback f).op.HasLeftKanExtension P]
    (K : DerivedCategory (Sheaf (topology S) AddCommGrpCat.{u + 1})),
    IsIsomorphic
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
        ((siteAbelianSectionsDerived (proetaleTopology.over S) (Over.mk f)).obj
          ((piExact S).mapDerivedCategory.obj K)))
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
        ((siteAbelianSectionsDerived (topology T) (globalProEt T)).obj
          ((smallInverseImage f).mapDerivedCategory.obj K))))

/- Lemma 61.17.3 (3): comparison of big and small pro-étale cohomology. -/
@[stacks 0F69] #check (AlgebraicGeometry.Scheme.ProEt.proetaleCohomology_relocalization :
  ∀ {S T : Scheme.{u}} (f : T ⟶ S) (n : ℤ)
    [HasSheafify (topology T) AddCommGrpCat.{u + 1}]
    [HasSheafify (proetaleTopology.over S) AddCommGrpCat.{u + 1}]
    [IsGrothendieckAbelian (Sheaf (topology T) AddCommGrpCat.{u + 1})]
    [IsGrothendieckAbelian (Sheaf (proetaleTopology.over S) AddCommGrpCat.{u + 1})]
    (M : DerivedCategory (Sheaf (proetaleTopology.over S) AddCommGrpCat.{u + 1})),
    IsIsomorphic
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
        ((siteAbelianSectionsDerived (proetaleTopology.over S) (Over.mk f)).obj M))
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
        ((siteAbelianSectionsDerived (topology T) (globalProEt T)).obj
          ((iInverseImage f).mapDerivedCategory.obj M))))

end AlgebraicGeometry.Scheme.ProEt
