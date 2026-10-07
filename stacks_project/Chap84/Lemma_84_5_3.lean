module

public import ReasLib.CategoryTheory.Sites.Over.Derived.BaseChange
public import stacks_project.Chap84.Lemma_84_5_3_Comparison
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Etale
open AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig
open AlgebraicGeometry.AlgebraicSpace.Etale.Derived
open AlgebraicGeometry.AlgebraicSpace.Etale.Module.Derived
open CategoryTheory.GrothendieckTopology.Derived.Over
open CategoryTheory.GrothendieckTopology.Derived.Over.BaseChange

noncomputable section

universe u

/- Lemma 84.5.3 (1) -/
@[stacks 0DGA] #check (@AlgebraicGeometry.AlgebraicSpace.Etale.Derived.directImageRestrict :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    [HasSheafify (smallEtaleTopology Y) AddCommGrpCat.{u + 1}]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasSheafify (overEtaleTopology Y) AddCommGrpCat.{u + 1}]
    [HasSheafify (overEtaleTopology X) AddCommGrpCat.{u + 1}]
    [IsGrothendieckAbelian (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
    [(sheafPushforwardAbelian f).Additive]
    [∀ P : (Over Y)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (Over.map f).op.HasPointwiseRightKanExtension P]
    (K : DerivedCategory (Sheaf (overEtaleTopology Y) AddCommGrpCat.{u + 1})),
    IsIsomorphic ((Derived.relocalization (𝟙 X)).obj ((Derived.bigDirectImage f).obj K))
      ((Derived.directImage f).obj ((Derived.relocalization (𝟙 Y)).obj K)))

/- Lemma 84.5.3 (2) -/
@[stacks 0DGA] #check (@AlgebraicGeometry.AlgebraicSpace.Etale.Module.Derived.directImageRestrict :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    [HasSheafify (smallEtaleTopology Y) AddCommGrpCat.{u + 1}]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasSheafify (overEtaleTopology Y) AddCommGrpCat.{u + 1}]
    [HasSheafify (overEtaleTopology X) AddCommGrpCat.{u + 1}]
    [Abelian Y.Modules] [Abelian X.Modules]
    [Abelian (SheafOfModules.{u} (overEtaleStructureSheaf Y))]
    [Abelian (SheafOfModules.{u} (overEtaleStructureSheaf X))]
    [IsGrothendieckAbelian Y.Modules] [IsGrothendieckAbelian X.Modules]
    [IsGrothendieckAbelian (SheafOfModules.{u} (overEtaleStructureSheaf Y))]
    [IsGrothendieckAbelian (SheafOfModules.{u} (overEtaleStructureSheaf X))]
    [HasDerivedCategory Y.Modules] [HasDerivedCategory X.Modules]
    [HasDerivedCategory (SheafOfModules.{u} (overEtaleStructureSheaf Y))]
    [HasDerivedCategory (SheafOfModules.{u} (overEtaleStructureSheaf X))]
    (K : DerivedCategory (SheafOfModules.{u} (overEtaleStructureSheaf Y))),
    IsIsomorphic
      ((Module.Derived.relocalization (𝟙 X)).obj ((Module.Derived.bigDirectImage f).obj K))
      ((Module.Derived.smallDirectImage f).obj ((Module.Derived.relocalization (𝟙 Y)).obj K)))

/- Lemma 84.5.3 (3) -/
@[stacks 0DGA] #check (@AlgebraicGeometry.AlgebraicSpace.Etale.Derived.directImageRelocalization :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {X' Y' : AlgebraicSpace S}
    (f : Y ⟶ X) (g : X' ⟶ X) (g' : Y' ⟶ Y) (f' : Y' ⟶ X')
    (hcart : IsPullback g' f' f g)
    [HasSheafify (smallEtaleTopology Y) AddCommGrpCat.{u + 1}]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasSheafify (smallEtaleTopology Y') AddCommGrpCat.{u + 1}]
    [HasSheafify (smallEtaleTopology X') AddCommGrpCat.{u + 1}]
    [HasSheafify (overEtaleTopology Y) AddCommGrpCat.{u + 1}]
    [HasSheafify (overEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasSheafify (overEtaleTopology Y') AddCommGrpCat.{u + 1}]
    [HasSheafify (overEtaleTopology X') AddCommGrpCat.{u + 1}]
    [IsGrothendieckAbelian (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
    [IsGrothendieckAbelian (Sheaf (smallEtaleTopology Y') AddCommGrpCat.{u + 1})]
    [(sheafPushforwardAbelian f').Additive]
    [∀ P : (Over Y)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (Over.map f).op.HasPointwiseRightKanExtension P]
    [∀ P : (Over Y')ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (Over.map f').op.HasPointwiseRightKanExtension P]
    (K : DerivedCategory (Sheaf (overEtaleTopology Y) AddCommGrpCat.{u + 1})),
    IsIsomorphic ((Derived.relocalization g).obj ((Derived.bigDirectImage f).obj K))
      ((Derived.directImage f').obj ((Derived.relocalization g').obj K)))

/- Lemma 84.5.3 (4) -/
@[stacks 0DGA] #check (@AlgebraicGeometry.AlgebraicSpace.Etale.Module.Derived.directImageRelocalization :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {X' Y' : AlgebraicSpace S}
    (f : Y ⟶ X) (g : X' ⟶ X) (g' : Y' ⟶ Y) (f' : Y' ⟶ X')
    (hcart : IsPullback g' f' f g)
    [HasSheafify (smallEtaleTopology Y) AddCommGrpCat.{u + 1}]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasSheafify (smallEtaleTopology Y') AddCommGrpCat.{u + 1}]
    [HasSheafify (smallEtaleTopology X') AddCommGrpCat.{u + 1}]
    [HasSheafify (overEtaleTopology Y) AddCommGrpCat.{u + 1}]
    [HasSheafify (overEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasSheafify (overEtaleTopology Y') AddCommGrpCat.{u + 1}]
    [HasSheafify (overEtaleTopology X') AddCommGrpCat.{u + 1}]
    [Abelian Y'.Modules] [Abelian X'.Modules]
    [Abelian (SheafOfModules.{u} (overEtaleStructureSheaf Y))]
    [Abelian (SheafOfModules.{u} (overEtaleStructureSheaf X))]
    [Abelian (SheafOfModules.{u} (overEtaleStructureSheaf Y'))]
    [IsGrothendieckAbelian Y'.Modules] [IsGrothendieckAbelian X'.Modules]
    [IsGrothendieckAbelian (SheafOfModules.{u} (overEtaleStructureSheaf Y))]
    [IsGrothendieckAbelian (SheafOfModules.{u} (overEtaleStructureSheaf X))]
    [HasDerivedCategory Y'.Modules] [HasDerivedCategory X'.Modules]
    [HasDerivedCategory (SheafOfModules.{u} (overEtaleStructureSheaf Y))]
    [HasDerivedCategory (SheafOfModules.{u} (overEtaleStructureSheaf X))]
    (K : DerivedCategory (SheafOfModules.{u} (overEtaleStructureSheaf Y))),
    IsIsomorphic
      ((Module.Derived.relocalization g).obj ((Module.Derived.bigDirectImage f).obj K))
      ((Module.Derived.smallDirectImage f').obj ((Module.Derived.relocalization g').obj K)))

section
variable {S : Scheme.{u}}

/- Lemma 84.5.3 (5) -/
@[stacks 0DGA] #check
  (@CategoryTheory.GrothendieckTopology.Derived.Over.BaseChange.appIso
    (AlgebraicSpace S) inferInstance
    (bigEtaleTopology : GrothendieckTopology (AlgebraicSpace S)) :
    ∀ {Y' Y X' X : AlgebraicSpace S}
      (g' : Y' ⟶ Y) (f' : Y' ⟶ X') (f : Y ⟶ X) (g : X' ⟶ X)
      [HasSheafify (bigEtaleTopology.over Y') AddCommGrpCat.{u + 1}]
      [HasSheafify (bigEtaleTopology.over Y) AddCommGrpCat.{u + 1}]
      [HasSheafify (bigEtaleTopology.over X') AddCommGrpCat.{u + 1}]
      [HasSheafify (bigEtaleTopology.over X) AddCommGrpCat.{u + 1}]
      [∀ P : (Over Y)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
        (Over.map f).op.HasPointwiseRightKanExtension P]
      [∀ P : (Over Y')ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
        (Over.map f').op.HasPointwiseRightKanExtension P]
      (hcart : IsPullback g' f' f g)
      (K : DerivedCategory (Sheaf (bigEtaleTopology.over Y) AddCommGrpCat.{u + 1})),
      (CategoryTheory.GrothendieckTopology.Derived.Over.pullback
          (bigEtaleTopology : GrothendieckTopology (AlgebraicSpace S)) g).obj
          ((CategoryTheory.GrothendieckTopology.Derived.Over.pushforward
            (bigEtaleTopology : GrothendieckTopology (AlgebraicSpace S)) f).obj K) ≅
        (CategoryTheory.GrothendieckTopology.Derived.Over.pushforward
            (bigEtaleTopology : GrothendieckTopology (AlgebraicSpace S)) f').obj
          ((CategoryTheory.GrothendieckTopology.Derived.Over.pullback
            (bigEtaleTopology : GrothendieckTopology (AlgebraicSpace S)) g').obj K))
end

/- Lemma 84.5.3 (6) -/
@[stacks 0DGA] #check (@AlgebraicGeometry.AlgebraicSpace.Etale.Module.Derived.bigBaseChange :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {X' Y' : AlgebraicSpace S}
    (f : Y ⟶ X) (g : X' ⟶ X) (g' : Y' ⟶ Y) (f' : Y' ⟶ X')
    (hcart : IsPullback g' f' f g)
    [HasSheafify (overEtaleTopology Y) AddCommGrpCat.{u + 1}]
    [HasSheafify (overEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasSheafify (overEtaleTopology Y') AddCommGrpCat.{u + 1}]
    [HasSheafify (overEtaleTopology X') AddCommGrpCat.{u + 1}]
    [Abelian (SheafOfModules.{u} (overEtaleStructureSheaf Y))]
    [Abelian (SheafOfModules.{u} (overEtaleStructureSheaf X))]
    [Abelian (SheafOfModules.{u} (overEtaleStructureSheaf Y'))]
    [Abelian (SheafOfModules.{u} (overEtaleStructureSheaf X'))]
    [IsGrothendieckAbelian (SheafOfModules.{u} (overEtaleStructureSheaf Y))]
    [IsGrothendieckAbelian (SheafOfModules.{u} (overEtaleStructureSheaf X))]
    [IsGrothendieckAbelian (SheafOfModules.{u} (overEtaleStructureSheaf Y'))]
    [IsGrothendieckAbelian (SheafOfModules.{u} (overEtaleStructureSheaf X'))]
    [HasDerivedCategory (SheafOfModules.{u} (overEtaleStructureSheaf Y))]
    [HasDerivedCategory (SheafOfModules.{u} (overEtaleStructureSheaf X))]
    [HasDerivedCategory (SheafOfModules.{u} (overEtaleStructureSheaf Y'))]
    [HasDerivedCategory (SheafOfModules.{u} (overEtaleStructureSheaf X'))]
    (K : DerivedCategory (SheafOfModules.{u} (overEtaleStructureSheaf Y))),
    IsIsomorphic
      ((Module.Derived.bigInverseImage g).obj ((Module.Derived.bigDirectImage f).obj K))
      ((Module.Derived.bigDirectImage f').obj ((Module.Derived.bigInverseImage g').obj K)))

end
