/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.HigherDirectImage

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- Module sheaves on an associated site carry the canonical abelian structure
of its associated ringed site. -/
noncomputable abbrev associatedModules_abelian {S : Scheme.{u}} {𝒳 : GroupoidsOver S}
    {σ : StandardTopology} :
    Abelian (SheafOfModules.{u + 1} (associatedStructureSheaf 𝒳 σ)) :=
  RingedSite.moduleCatAbelian.{u + 1, u + 1, u, u} (associatedRingedSite 𝒳 σ)

end AlgebraicGeometry.GroupoidsOver

/- The associated-site pushforward functors retain their public mathematical API. -/
#check (AlgebraicGeometry.GroupoidsOver.abelianPushforward :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y) (τ : StandardTopology),
    Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1} ⥤
      Sheaf (Y.associatedTopology τ) AddCommGrpCat.{u + 1})

#check (AlgebraicGeometry.GroupoidsOver.modulePushforward :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y) (τ : StandardTopology),
    [HasSheafify (X.associatedTopology τ) AddCommGrpCat.{u + 1}] →
    [HasSheafify (Y.associatedTopology τ) AddCommGrpCat.{u + 1}] →
    SheafOfModules.{u + 1} (GroupoidsOver.associatedStructureSheaf X τ) ⥤
      SheafOfModules.{u + 1} (GroupoidsOver.associatedStructureSheaf Y τ))

#check (AlgebraicGeometry.GroupoidsOver.higherDirectImageFunctor :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y) (τ : StandardTopology),
    [HasSheafify (X.associatedTopology τ) AddCommGrpCat.{u + 1}] →
    [HasSheafify (Y.associatedTopology τ) AddCommGrpCat.{u + 1}] →
    [HasInjectiveResolutions (Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1})] →
    ℕ → Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1} ⥤
      Sheaf (Y.associatedTopology τ) AddCommGrpCat.{u + 1})

#check (AlgebraicGeometry.GroupoidsOver.higherDirectImageModuleFunctor :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y) (τ : StandardTopology),
    [HasSheafify (X.associatedTopology τ) AddCommGrpCat.{u + 1}] →
    [HasSheafify (Y.associatedTopology τ) AddCommGrpCat.{u + 1}] →
    ℕ → SheafOfModules.{u + 1} (GroupoidsOver.associatedStructureSheaf X τ) ⥤
      SheafOfModules.{u + 1} (GroupoidsOver.associatedStructureSheaf Y τ))
