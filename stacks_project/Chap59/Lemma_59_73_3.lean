/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible.Descent
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u w

namespace CategoryTheory.Sheaf

variable {X Y : Scheme.{u}}
variable [CompactSpace X] [QuasiSeparatedSpace X]
variable [CompactSpace Y] [QuasiSeparatedSpace Y]

/- Lemma 59.73.3 (1): surjective pullback detects constructibility of étale sheaves of sets
over quasi-compact and quasi-separated schemes. -/
@[stacks 095Q] #check
  (CategoryTheory.Sheaf.isConstructibleEtaleSet_iff_smallEtaleInverseImage :
    ∀ {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      [CompactSpace Y] [QuasiSeparatedSpace Y] (f : X ⟶ Y) [Surjective f]
      [∀ Z : Scheme.{u}, HasWeakSheafify Z.smallEtaleTopology (Type (u + 1))]
      [∀ (Z W : Scheme.{u}) (g : Z ⟶ W) (P : W.Etaleᵒᵖ ⥤ Type (u + 1)),
        (Scheme.smallEtalePullback g).op.HasLeftKanExtension P]
      (F : Sheaf Y.smallEtaleTopology (Type (u + 1))),
      IsConstructibleEtaleSet (X := Y)
        (fun {Z} g ↦ (smallEtaleInverseImage g (Type (u + 1))).obj)
        (fun {Z} G ↦ IsFiniteLocallyConstant G) F ↔
      IsConstructibleEtaleSet (X := X)
        (fun {Z} g ↦ (smallEtaleInverseImage g (Type (u + 1))).obj)
        (fun {Z} G ↦ IsFiniteLocallyConstant G)
        ((smallEtaleInverseImage f (Type (u + 1))).obj F))

/- Lemma 59.73.3 (2): surjective pullback detects constructibility of étale abelian sheaves
over quasi-compact and quasi-separated schemes. -/
@[stacks 095Q] #check
  (CategoryTheory.Sheaf.isConstructibleEtaleAddCommGrp_iff_smallEtaleInverseImage :
    ∀ {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      [CompactSpace Y] [QuasiSeparatedSpace Y] (f : X ⟶ Y) [Surjective f]
      [∀ Z : Scheme.{u}, HasWeakSheafify Z.smallEtaleTopology AddCommGrpCat.{u + 1}]
      [∀ (Z W : Scheme.{u}) (g : Z ⟶ W) (P : W.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}),
        (Scheme.smallEtalePullback g).op.HasLeftKanExtension P]
      (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}),
      IsConstructibleEtaleAddCommGrp (X := Y)
        (fun {Z} g ↦ (smallEtaleInverseImage g AddCommGrpCat.{u + 1}).obj)
        (fun {Z} G ↦ IsFiniteLocallyConstantAddCommGrp G) F ↔
      IsConstructibleEtaleAddCommGrp (X := X)
        (fun {Z} g ↦ (smallEtaleInverseImage g AddCommGrpCat.{u + 1}).obj)
        (fun {Z} G ↦ IsFiniteLocallyConstantAddCommGrp G)
        ((smallEtaleInverseImage f AddCommGrpCat.{u + 1}).obj F))

/- Lemma 59.73.3 (3): surjective pullback detects constructibility of étale sheaves of
modules over a Noetherian ring on quasi-compact and quasi-separated schemes. -/
@[stacks 095Q] #check
  (CategoryTheory.Sheaf.isConstructibleEtaleModule_iff_smallEtaleInverseImage :
    ∀ {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      [CompactSpace Y] [QuasiSeparatedSpace Y] (f : X ⟶ Y) [Surjective f]
      {Λ : Type w} [Ring Λ] [IsNoetherianRing Λ]
      [∀ Z : Scheme.{u}, HasWeakSheafify Z.smallEtaleTopology (ModuleCat.{w} Λ)]
      [∀ (Z : Scheme.{u}) (U : Z.Etale),
        HasWeakSheafify (Z.smallEtaleTopology.over U) (ModuleCat.{w} Λ)]
      [∀ (Z W : Scheme.{u}) (g : Z ⟶ W) (P : W.Etaleᵒᵖ ⥤ ModuleCat.{w} Λ),
        (Scheme.smallEtalePullback g).op.HasLeftKanExtension P]
      (F : Sheaf Y.smallEtaleTopology (ModuleCat.{w} Λ)),
      IsConstructibleEtaleModule (X := Y)
        (fun {Z} g ↦ (smallEtaleInverseImage g (ModuleCat.{w} Λ)).obj)
        (fun {Z} G ↦ IsFiniteTypeLocallyConstantModule G) F ↔
      IsConstructibleEtaleModule (X := X)
        (fun {Z} g ↦ (smallEtaleInverseImage g (ModuleCat.{w} Λ)).obj)
        (fun {Z} G ↦ IsFiniteTypeLocallyConstantModule G)
        ((smallEtaleInverseImage f (ModuleCat.{w} Λ)).obj F))

end CategoryTheory.Sheaf
