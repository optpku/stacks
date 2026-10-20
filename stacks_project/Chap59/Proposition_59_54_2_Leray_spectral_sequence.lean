/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Leray
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor.RightDerived
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/- Proposition 59.54.2 (Leray spectral sequence): the étale Leray spectral sequence
of an abelian étale sheaf exists. -/
@[stacks 03QC] #check
  (AlgebraicGeometry.Scheme.Etale.etaleLeray_nonempty :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
      [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
      [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
      [Abelian (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
      [Abelian (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
      [HasDerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
      [HasDerivedCategory (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
      [HasDerivedCategory AddCommGrpCat.{u}]
      [EnoughInjectives (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
      [EnoughInjectives (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
      [HasInjectiveResolutions (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
      [HasInjectiveResolutions (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
      [(etaleAbelianPushforward f).Additive]
      [HasTerminal Y.Etale] [HasTerminal X.Etale]
      [(siteAbelianSectionsFunctor Y.smallEtaleTopology (terminal Y.Etale)).Additive]
      [(siteAbelianSectionsFunctor X.smallEtaleTopology (terminal X.Etale)).Additive],
      Nonempty (etaleLeray f F))

#check
  (AlgebraicGeometry.Scheme.Etale.etaleLeray_pageTwo_isIsomorphic :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
      [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
      [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
      [Abelian (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
      [Abelian (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
      [HasDerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
      [HasDerivedCategory (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
      [HasDerivedCategory AddCommGrpCat.{u}]
      [EnoughInjectives (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
      [EnoughInjectives (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
      [HasInjectiveResolutions (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
      [HasInjectiveResolutions (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
      [(etaleAbelianPushforward f).Additive]
      [HasTerminal Y.Etale] [HasTerminal X.Etale]
      [(siteAbelianSectionsFunctor Y.smallEtaleTopology (terminal Y.Etale)).Additive]
      [(siteAbelianSectionsFunctor X.smallEtaleTopology (terminal X.Etale)).Additive]
      (p q : ℕ),
      IsIsomorphic (etaleLeray_pageTwo f F p q)
        (etaleCohomology Y (etaleHigherDirectImage f F q) p))

#check
  (AlgebraicGeometry.Scheme.Etale.etaleLeray_abutment_isIsomorphic :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
      [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
      [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
      [Abelian (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
      [Abelian (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
      [HasDerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
      [HasDerivedCategory (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
      [HasDerivedCategory AddCommGrpCat.{u}]
      [EnoughInjectives (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
      [EnoughInjectives (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
      [HasInjectiveResolutions (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
      [HasInjectiveResolutions (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
      [(etaleAbelianPushforward f).Additive]
      [HasTerminal Y.Etale] [HasTerminal X.Etale]
      [(siteAbelianSectionsFunctor Y.smallEtaleTopology (terminal Y.Etale)).Additive]
      [(siteAbelianSectionsFunctor X.smallEtaleTopology (terminal X.Etale)).Additive]
      (n : ℕ),
      IsIsomorphic (etaleLeray_abutment f F n) (etaleCohomology X F n))

end AlgebraicGeometry.Scheme.Etale
