module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Underlying
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Derived.Pushforward
public import ReasLib.CategoryTheory.Sites.Derived.Sections
public import ReasLib.CategoryTheory.Sites.GlobalSections.Additive
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived global sections and morphisms of ringed topoi

The comparison in this file is presentation-independent: its input is an arbitrary
`RingedSite.ToposHom`.  Module structure is forgotten only after taking derived direct image, so
the result is the functorial abelian-group-valued form of derived global sections.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe uX vX uY vY w

namespace RingedSite.ToposHom.ModuleSections

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
variable [X.siteTopology.HasSheafCompose (forget RingCat.{w})]
  [Y.siteTopology.HasSheafCompose (forget RingCat.{w})]

/-- Derived global sections of modules after forgetting to the underlying additive sheaf. -/
@[stacks 08J6 "abelian derived global sections of modules"]
noncomputable abbrev derivedGlobalSections
    (X : RingedSite.{uX, vX, w})
    [UnivLE.{max uX vX, w}]
    [HasSheafify X.siteTopology AddCommGrpCat.{w}]
    [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor X.siteTopology AddCommGrpCat.{w}]
    [IsGrothendieckAbelian (Sheaf X.siteTopology AddCommGrpCat.{w})] :
    RingedSite.Hom.ModuleDerived.{w} X ⥤ DerivedCategory AddCommGrpCat.{w} :=
  RingedSite.Hom.underlyingAbelianSheafDerived.{w} X ⋙
    Functor.RightDerived.Cochain.functor
      (Sheaf.Γ X.siteTopology AddCommGrpCat.{w})

/-- Remark 21.14.4 (08J6): for an arbitrary morphism `f` of site-presented ringed topoi,
derived global sections after `Rf_*` are functorially isomorphic to derived global sections on the
source after forgetting module structure. -/
@[stacks 08J6]
theorem pushforward_isomorphic
    (f : RingedSite.ToposHom X Y)
    [UnivLE.{max uX vX, w}] [UnivLE.{max uY vY, w}]
    [f.HasModulePushforwardDerived]
    [HasSheafify X.siteTopology AddCommGrpCat.{w}]
    [HasSheafify Y.siteTopology AddCommGrpCat.{w}]
    [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [Y.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor X.siteTopology AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor Y.siteTopology AddCommGrpCat.{w}]
    [IsGrothendieckAbelian (RingedSite.ModuleCat.{w} X)]
    [IsGrothendieckAbelian (Sheaf X.siteTopology AddCommGrpCat.{w})]
    [IsGrothendieckAbelian (Sheaf Y.siteTopology AddCommGrpCat.{w})] :
    IsIsomorphic
      (f.modulePushforwardDerived ⋙ derivedGlobalSections Y)
      (derivedGlobalSections X) := sorry

end RingedSite.ToposHom.ModuleSections
