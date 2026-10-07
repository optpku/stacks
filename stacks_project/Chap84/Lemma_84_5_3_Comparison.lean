module

public import stacks_project.Chap84.Lemma_84_5_3_Derived
public import stacks_project.Chap84.Lemma_84_5_3_Module

/-!
# Derived comparison of big and small étale direct images of algebraic spaces

Restriction from `(Spaces/Y)_étale` to the small étale sites identifies the
unbounded derived direct images, including after mixed small/big restriction
along a fibre-product square.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig
open AlgebraicGeometry.AlgebraicSpace.Etale.Derived
open AlgebraicGeometry.AlgebraicSpace.Etale.Module.Derived

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Etale.Derived

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Restriction of a big étale derived direct image agrees with small-site direct image. -/
theorem directImageRestrict (f : Y ⟶ X)
    [HasSheafify (smallEtaleTopology Y) AddCommGrpCat.{u + 1}]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasSheafify (overEtaleTopology Y) AddCommGrpCat.{u + 1}]
    [HasSheafify (overEtaleTopology X) AddCommGrpCat.{u + 1}]
    [IsGrothendieckAbelian (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
    [(sheafPushforwardAbelian f).Additive]
    [∀ P : (Over Y)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (Over.map f).op.HasPointwiseRightKanExtension P]
    (K : DerivedCategory (Sheaf (overEtaleTopology Y) AddCommGrpCat.{u + 1})) :
    IsIsomorphic ((relocalization (𝟙 X)).obj ((bigDirectImage f).obj K))
      ((directImage f).obj ((relocalization (𝟙 Y)).obj K)) :=
  sorry

/-- Derived restriction commutes with direct image across an arbitrary cartesian square. -/
theorem directImageRelocalization
    {X' Y' : AlgebraicSpace S} (f : Y ⟶ X) (g : X' ⟶ X)
    (g' : Y' ⟶ Y) (f' : Y' ⟶ X') (hcart : IsPullback g' f' f g)
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
    (K : DerivedCategory (Sheaf (overEtaleTopology Y) AddCommGrpCat.{u + 1})) :
    IsIsomorphic ((relocalization g).obj ((bigDirectImage f).obj K))
      ((directImage f').obj ((relocalization g').obj K)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Etale.Derived

namespace AlgebraicGeometry.AlgebraicSpace.Etale.Module.Derived

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Restriction of a big étale module direct image agrees with small-site direct image. -/
theorem directImageRestrict (f : Y ⟶ X)
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
    (K : DerivedCategory (SheafOfModules.{u} (overEtaleStructureSheaf Y))) :
    IsIsomorphic ((relocalization (𝟙 X)).obj ((bigDirectImage f).obj K))
      ((smallDirectImage f).obj ((relocalization (𝟙 Y)).obj K)) :=
  sorry

/-- Restriction commutes with module direct image across an arbitrary cartesian square. -/
theorem directImageRelocalization
    {X' Y' : AlgebraicSpace S} (f : Y ⟶ X) (g : X' ⟶ X)
    (g' : Y' ⟶ Y) (f' : Y' ⟶ X') (hcart : IsPullback g' f' f g)
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
    (K : DerivedCategory (SheafOfModules.{u} (overEtaleStructureSheaf Y))) :
    IsIsomorphic ((relocalization g).obj ((bigDirectImage f).obj K))
      ((smallDirectImage f').obj ((relocalization g').obj K)) :=
  sorry

/-- Big étale module inverse image commutes with derived direct image on a cartesian square.
The target is the derived category of modules on the big ringed site
`(Spaces/X')_étale`, matching Cohomology on Sites, Lemma 21.21.2. -/
theorem bigBaseChange
    {X' Y' : AlgebraicSpace S} (f : Y ⟶ X) (g : X' ⟶ X)
    (g' : Y' ⟶ Y) (f' : Y' ⟶ X') (hcart : IsPullback g' f' f g)
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
    (K : DerivedCategory (SheafOfModules.{u} (overEtaleStructureSheaf Y))) :
    IsIsomorphic ((bigInverseImage g).obj ((bigDirectImage f).obj K))
      ((bigDirectImage f').obj ((bigInverseImage g').obj K)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Etale.Module.Derived

end
