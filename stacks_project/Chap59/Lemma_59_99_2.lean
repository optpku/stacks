/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Module.Derived.Comparison
public import ReasLib.CategoryTheory.Sites.Over.Derived.BaseChange
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale
open AlgebraicGeometry.Scheme.Etale.Small
open AlgebraicGeometry.Scheme.Etale.Derived
open AlgebraicGeometry.Scheme.Etale.Module.Derived
open CategoryTheory.GrothendieckTopology.Derived.Over
open CategoryTheory.GrothendieckTopology.Derived.Over.BaseChange

noncomputable section

universe u v

/- Lemma 59.99.2 (1) -/
@[stacks 075A] #check (@AlgebraicGeometry.Scheme.Etale.Derived.directImageRestrict :
  ∀ {S T : Scheme.{u}}
    (f : T ⟶ S)
    [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasSheafify (T.overGrothendieckTopology @Etale) AddCommGrpCat.{u + 1}]
    [HasSheafify (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u + 1}]
    [IsGrothendieckAbelian (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        S.smallEtaleTopology T.smallEtaleTopology).Additive]
    [∀ P : (Over T)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (Over.map f).op.HasPointwiseRightKanExtension P]
    (K : DerivedCategory
      (Sheaf (T.overGrothendieckTopology @Etale) AddCommGrpCat.{u + 1})),
    IsIsomorphic ((AlgebraicGeometry.Scheme.Etale.Derived.relocalization (𝟙 S)).obj
        ((CategoryTheory.GrothendieckTopology.Derived.Over.pushforward
          Scheme.etaleTopology f).obj K))
      ((AlgebraicGeometry.Scheme.Etale.Derived.directImage f).obj
        ((AlgebraicGeometry.Scheme.Etale.Derived.relocalization (𝟙 T)).obj K)))

/- Lemma 59.99.2 (2) -/
@[stacks 075A] #check (@AlgebraicGeometry.Scheme.Etale.Module.Derived.directImageRestrict :
  ∀ {S T : Scheme.{u}}
    (f : T ⟶ S) [UnivLE.{u + 1, v}]
    [HasSheafify T.smallEtaleTopology AddCommGrpCat.{v}]
    [T.smallEtaleTopology.WEqualsLocallyBijective AddCommGrpCat.{v}]
    [HasSheafify S.smallEtaleTopology AddCommGrpCat.{v}]
    [S.smallEtaleTopology.WEqualsLocallyBijective AddCommGrpCat.{v}]
    [HasSheafify (T.overGrothendieckTopology @Etale) AddCommGrpCat.{v}]
    [(T.overGrothendieckTopology @Etale).WEqualsLocallyBijective AddCommGrpCat.{v}]
    [HasSheafify (S.overGrothendieckTopology @Etale) AddCommGrpCat.{v}]
    [(S.overGrothendieckTopology @Etale).WEqualsLocallyBijective AddCommGrpCat.{v}]
    [IsGrothendieckAbelian (SheafOfModules.{v} (Small.structureSheaf T))]
    [IsGrothendieckAbelian (SheafOfModules.{v} (Small.structureSheaf S))]
    [IsGrothendieckAbelian
      (SheafOfModules.{v} (StandardTopology.Big.structureSheaf .etale T))]
    [IsGrothendieckAbelian
      (SheafOfModules.{v} (StandardTopology.Big.structureSheaf .etale S))]
    [HasDerivedCategory (SheafOfModules.{v} (Small.structureSheaf T))]
    [HasDerivedCategory (SheafOfModules.{v} (Small.structureSheaf S))]
    [HasDerivedCategory
      (SheafOfModules.{v} (StandardTopology.Big.structureSheaf .etale T))]
    [HasDerivedCategory
      (SheafOfModules.{v} (StandardTopology.Big.structureSheaf .etale S))]
    [(AlgebraicGeometry.Scheme.Etale.Module.smallDirectImage f).Additive] [(AlgebraicGeometry.Scheme.Etale.Module.bigDirectImage f).Additive]
    (K : DerivedCategory
      (SheafOfModules.{v} (StandardTopology.Big.structureSheaf .etale T))),
    IsIsomorphic
      ((AlgebraicGeometry.Scheme.Etale.Module.Derived.relocalization (𝟙 S)).obj ((AlgebraicGeometry.Scheme.Etale.Module.Derived.bigDirectImage f).obj K))
      ((AlgebraicGeometry.Scheme.Etale.Module.Derived.smallDirectImage f).obj ((AlgebraicGeometry.Scheme.Etale.Module.Derived.relocalization (𝟙 T)).obj K)))

/- Lemma 59.99.2 (3) -/
@[stacks 075A] #check (@AlgebraicGeometry.Scheme.Etale.Derived.directImageRelocalization :
  ∀ {S T : Scheme.{u}}
    {S' T' : Scheme.{u}} (f : T ⟶ S) (g : S' ⟶ S)
    (g' : T' ⟶ T) (f' : T' ⟶ S') (hcart : IsPullback g' f' f g)
    [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasSheafify T'.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasSheafify S'.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasSheafify (T.overGrothendieckTopology @Etale) AddCommGrpCat.{u + 1}]
    [HasSheafify (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u + 1}]
    [HasSheafify (T'.overGrothendieckTopology @Etale) AddCommGrpCat.{u + 1}]
    [HasSheafify (S'.overGrothendieckTopology @Etale) AddCommGrpCat.{u + 1}]
    [IsGrothendieckAbelian (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [IsGrothendieckAbelian (Sheaf T'.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [((smallEtalePullback f').sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        S'.smallEtaleTopology T'.smallEtaleTopology).Additive]
    [∀ P : (Over T)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (Over.map f).op.HasPointwiseRightKanExtension P]
    [∀ P : (Over T')ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (Over.map f').op.HasPointwiseRightKanExtension P]
    (K : DerivedCategory
      (Sheaf (T.overGrothendieckTopology @Etale) AddCommGrpCat.{u + 1})),
    IsIsomorphic ((AlgebraicGeometry.Scheme.Etale.Derived.relocalization g).obj
        ((CategoryTheory.GrothendieckTopology.Derived.Over.pushforward
          Scheme.etaleTopology f).obj K))
      ((AlgebraicGeometry.Scheme.Etale.Derived.directImage f').obj
        ((AlgebraicGeometry.Scheme.Etale.Derived.relocalization g').obj K)))

/- Lemma 59.99.2 (4) -/
@[stacks 075A] #check (@AlgebraicGeometry.Scheme.Etale.Module.Derived.directImageRelocalization :
  ∀ {S T : Scheme.{u}}
    {S' T' : Scheme.{u}} (f : T ⟶ S) (g : S' ⟶ S)
    (g' : T' ⟶ T) (f' : T' ⟶ S') (hcart : IsPullback g' f' f g)
    [UnivLE.{u + 1, v}]
    [HasSheafify T.smallEtaleTopology AddCommGrpCat.{v}]
    [T.smallEtaleTopology.WEqualsLocallyBijective AddCommGrpCat.{v}]
    [HasSheafify S.smallEtaleTopology AddCommGrpCat.{v}]
    [S.smallEtaleTopology.WEqualsLocallyBijective AddCommGrpCat.{v}]
    [HasSheafify T'.smallEtaleTopology AddCommGrpCat.{v}]
    [T'.smallEtaleTopology.WEqualsLocallyBijective AddCommGrpCat.{v}]
    [HasSheafify S'.smallEtaleTopology AddCommGrpCat.{v}]
    [S'.smallEtaleTopology.WEqualsLocallyBijective AddCommGrpCat.{v}]
    [HasSheafify (T.overGrothendieckTopology @Etale) AddCommGrpCat.{v}]
    [(T.overGrothendieckTopology @Etale).WEqualsLocallyBijective AddCommGrpCat.{v}]
    [HasSheafify (S.overGrothendieckTopology @Etale) AddCommGrpCat.{v}]
    [(S.overGrothendieckTopology @Etale).WEqualsLocallyBijective AddCommGrpCat.{v}]
    [HasSheafify (T'.overGrothendieckTopology @Etale) AddCommGrpCat.{v}]
    [(T'.overGrothendieckTopology @Etale).WEqualsLocallyBijective AddCommGrpCat.{v}]
    [HasSheafify (S'.overGrothendieckTopology @Etale) AddCommGrpCat.{v}]
    [(S'.overGrothendieckTopology @Etale).WEqualsLocallyBijective AddCommGrpCat.{v}]
    [IsGrothendieckAbelian (SheafOfModules.{v} (Small.structureSheaf T'))]
    [IsGrothendieckAbelian (SheafOfModules.{v} (Small.structureSheaf S'))]
    [IsGrothendieckAbelian
      (SheafOfModules.{v} (StandardTopology.Big.structureSheaf .etale T))]
    [IsGrothendieckAbelian
      (SheafOfModules.{v} (StandardTopology.Big.structureSheaf .etale S))]
    [HasDerivedCategory (SheafOfModules.{v} (Small.structureSheaf T'))]
    [HasDerivedCategory (SheafOfModules.{v} (Small.structureSheaf S'))]
    [HasDerivedCategory
      (SheafOfModules.{v} (StandardTopology.Big.structureSheaf .etale T))]
    [HasDerivedCategory
      (SheafOfModules.{v} (StandardTopology.Big.structureSheaf .etale S))]
    [(AlgebraicGeometry.Scheme.Etale.Module.smallDirectImage f').Additive] [(AlgebraicGeometry.Scheme.Etale.Module.bigDirectImage f).Additive]
    (K : DerivedCategory
      (SheafOfModules.{v} (StandardTopology.Big.structureSheaf .etale T))),
    IsIsomorphic
      ((AlgebraicGeometry.Scheme.Etale.Module.Derived.relocalization g).obj ((AlgebraicGeometry.Scheme.Etale.Module.Derived.bigDirectImage f).obj K))
      ((AlgebraicGeometry.Scheme.Etale.Module.Derived.smallDirectImage f').obj ((AlgebraicGeometry.Scheme.Etale.Module.Derived.relocalization g').obj K)))

/- Lemma 59.99.2 (5) -/
@[stacks 075A] #check
  (@CategoryTheory.GrothendieckTopology.Derived.Over.BaseChange.appIso
    Scheme.{u} inferInstance Scheme.etaleTopology :
    ∀ {T' T S' S : Scheme.{u}}
      (g' : T' ⟶ T) (f' : T' ⟶ S') (f : T ⟶ S) (g : S' ⟶ S)
      [HasSheafify (Scheme.etaleTopology.over T') AddCommGrpCat.{u + 1}]
      [HasSheafify (Scheme.etaleTopology.over T) AddCommGrpCat.{u + 1}]
      [HasSheafify (Scheme.etaleTopology.over S') AddCommGrpCat.{u + 1}]
      [HasSheafify (Scheme.etaleTopology.over S) AddCommGrpCat.{u + 1}]
      [∀ P : (Over T)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
        (Over.map f).op.HasPointwiseRightKanExtension P]
      [∀ P : (Over T')ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
        (Over.map f').op.HasPointwiseRightKanExtension P]
      (hcart : IsPullback g' f' f g)
      (K : DerivedCategory (Sheaf (Scheme.etaleTopology.over T) AddCommGrpCat.{u + 1})),
      (CategoryTheory.GrothendieckTopology.Derived.Over.pullback Scheme.etaleTopology g).obj
          ((CategoryTheory.GrothendieckTopology.Derived.Over.pushforward Scheme.etaleTopology f).obj K) ≅
        (CategoryTheory.GrothendieckTopology.Derived.Over.pushforward Scheme.etaleTopology f').obj
          ((CategoryTheory.GrothendieckTopology.Derived.Over.pullback Scheme.etaleTopology g').obj K))

/- Lemma 59.99.2 (6) -/
@[stacks 075A] #check (@AlgebraicGeometry.Scheme.Etale.Module.Derived.bigBaseChange :
  ∀ {S T : Scheme.{u}}
    {S' T' : Scheme.{u}} (f : T ⟶ S) (g : S' ⟶ S)
    (g' : T' ⟶ T) (f' : T' ⟶ S') (hcart : IsPullback g' f' f g)
    [UnivLE.{u + 1, v}]
    [HasSheafify (T.overGrothendieckTopology @Etale) AddCommGrpCat.{v}]
    [(T.overGrothendieckTopology @Etale).WEqualsLocallyBijective AddCommGrpCat.{v}]
    [HasSheafify (S.overGrothendieckTopology @Etale) AddCommGrpCat.{v}]
    [(S.overGrothendieckTopology @Etale).WEqualsLocallyBijective AddCommGrpCat.{v}]
    [HasSheafify (T'.overGrothendieckTopology @Etale) AddCommGrpCat.{v}]
    [(T'.overGrothendieckTopology @Etale).WEqualsLocallyBijective AddCommGrpCat.{v}]
    [HasSheafify (S'.overGrothendieckTopology @Etale) AddCommGrpCat.{v}]
    [(S'.overGrothendieckTopology @Etale).WEqualsLocallyBijective AddCommGrpCat.{v}]
    [IsGrothendieckAbelian
      (SheafOfModules.{v} (StandardTopology.Big.structureSheaf .etale T))]
    [IsGrothendieckAbelian
      (SheafOfModules.{v} (StandardTopology.Big.structureSheaf .etale S))]
    [IsGrothendieckAbelian
      (SheafOfModules.{v} (StandardTopology.Big.structureSheaf .etale T'))]
    [IsGrothendieckAbelian
      (SheafOfModules.{v} (StandardTopology.Big.structureSheaf .etale S'))]
    [HasDerivedCategory
      (SheafOfModules.{v} (StandardTopology.Big.structureSheaf .etale T))]
    [HasDerivedCategory
      (SheafOfModules.{v} (StandardTopology.Big.structureSheaf .etale S))]
    [HasDerivedCategory
      (SheafOfModules.{v} (StandardTopology.Big.structureSheaf .etale T'))]
    [HasDerivedCategory
      (SheafOfModules.{v} (StandardTopology.Big.structureSheaf .etale S'))]
    [(AlgebraicGeometry.Scheme.Etale.Module.bigDirectImage f).Additive] [(AlgebraicGeometry.Scheme.Etale.Module.bigDirectImage f').Additive]
    (K : DerivedCategory
      (SheafOfModules.{v} (StandardTopology.Big.structureSheaf .etale T))),
    IsIsomorphic
      ((AlgebraicGeometry.Scheme.Etale.Module.Derived.bigInverseImage g).obj ((AlgebraicGeometry.Scheme.Etale.Module.Derived.bigDirectImage f).obj K))
      ((AlgebraicGeometry.Scheme.Etale.Module.Derived.bigDirectImage f').obj ((AlgebraicGeometry.Scheme.Etale.Module.Derived.bigInverseImage g').obj K)))

end
