/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.SpectralSequence.Grothendieck
public import ReasLib.CategoryTheory.Sites.Derived.Sections
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Acyclicity

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor.RightDerived
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
variable [Abelian (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
variable [Abelian (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasDerivedCategory AddCommGrpCat.{u}]
variable [EnoughInjectives (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
variable [EnoughInjectives (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasInjectiveResolutions (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasInjectiveResolutions (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
variable [(etaleAbelianPushforward f).Additive]
variable [HasTerminal Y.Etale] [HasTerminal X.Etale]
variable [(siteAbelianSectionsFunctor Y.smallEtaleTopology (terminal Y.Etale)).Additive]
variable [(siteAbelianSectionsFunctor X.smallEtaleTopology (terminal X.Etale)).Additive]

/-- Canonical Grothendieck realization of étale Leray for abelian sheaves along `f`. -/
abbrev etaleLeray :=
  Grothendieck.canonical (etaleAbelianPushforward f)
    (siteAbelianSectionsFunctor Y.smallEtaleTopology (terminal Y.Etale))
    ((DerivedCategory.Plus.singleFunctor
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) 0).obj F)

/-- Canonical `(p, q)` second-page target of étale Leray. -/
abbrev etaleLeray_pageTwo (p : ℕ) (q : ℤ) : AddCommGrpCat.{u} :=
  Grothendieck.pageTwo
    (siteAbelianSectionsFunctor Y.smallEtaleTopology (terminal Y.Etale))
    (Bounded.functor (etaleAbelianPushforward f))
    ((DerivedCategory.Plus.singleFunctor
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) 0).obj F) p q

/-- Canonical degree-`n` abutment of étale Leray. -/
abbrev etaleLeray_abutment (n : ℤ) : AddCommGrpCat.{u} :=
  Grothendieck.abutment
    (Bounded.functor
      (etaleAbelianPushforward f ⋙
        siteAbelianSectionsFunctor Y.smallEtaleTopology (terminal Y.Etale)))
    ((DerivedCategory.Plus.singleFunctor
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) 0).obj F) n

/-- The degree-`q` right-derived direct image of an abelian small-étale sheaf along `f`. -/
abbrev etaleHigherDirectImage (q : ℕ) :
    Sheaf Y.smallEtaleTopology AddCommGrpCat.{u} :=
  ((etaleAbelianPushforward f).rightDerived q).obj F

/-- Étale cohomology of an abelian sheaf on the small étale site of `S`. -/
abbrev etaleCohomology (S : Scheme.{u})
    [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
    [Abelian (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})]
    [HasInjectiveResolutions (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})]
    [HasTerminal S.Etale]
    [(siteAbelianSectionsFunctor S.smallEtaleTopology (terminal S.Etale)).Additive]
    (G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ) :
    AddCommGrpCat.{u} :=
  ((siteAbelianSectionsFunctor S.smallEtaleTopology (terminal S.Etale)).rightDerived n).obj G

/-- The étale Leray spectral sequence of an abelian étale sheaf exists. -/
theorem etaleLeray_nonempty : Nonempty (etaleLeray f F) := sorry

/-- The second page of étale Leray is étale cohomology of the higher direct image. -/
theorem etaleLeray_pageTwo_isIsomorphic (p q : ℕ) :
    IsIsomorphic (etaleLeray_pageTwo f F p q)
      (etaleCohomology Y (etaleHigherDirectImage f F q) p) := sorry

/-- The abutment of étale Leray is étale cohomology of the original sheaf. -/
theorem etaleLeray_abutment_isIsomorphic (n : ℕ) :
    IsIsomorphic (etaleLeray_abutment f F n) (etaleCohomology X F n) := sorry

end AlgebraicGeometry.Scheme.Etale
