/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.UniversalQuasiIso
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Adequacy.Adjunction
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Adequacy.Category
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Below.Basic

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry

noncomputable section

universe u

namespace SheafOfModules.Adeq.associated

/-- Association from quasicoherent modules to adequate modules is additive. -/
instance additive (S : Scheme.{u}) (tau : StandardTopology) :
    (SheafOfModules.Adeq.associated S tau).Additive := sorry

end SheafOfModules.Adeq.associated

namespace SheafOfModules.Adeq

/-- Adequate modules on the big site of an affine scheme, relative to a
standard topology. -/
abbrev affineAdeq (tau : StandardTopology) (A : CommRingCat.{u}) :=
  SheafOfModules.Adeq ModuleValuedFunctor.tensorExtensionUnderlying
    (@affineEvaluationUnderlying (Scheme.Spec.obj (op A)) tau)

/-- Adequate modules on the big site of an affine scheme form an abelian category. -/
noncomputable instance affineAdeq.abelian (tau : StandardTopology) (A : CommRingCat.{u}) :
    Abelian (affineAdeq tau A) :=
  instAbelian (Scheme.Spec.obj (op A)) tau

/-- Association from quasicoherent modules on `Spec A` to adequate modules. -/
abbrev associatedAffine (tau : StandardTopology) (A : CommRingCat.{u}) :
    Scheme.QCoh (Scheme.Spec.obj (op A)) ⥤ affineAdeq tau A :=
  associated (Scheme.Spec.obj (op A)) tau

/-- Affine association is additive. -/
instance associatedAffine.additive (tau : StandardTopology) (A : CommRingCat.{u}) :
    (associatedAffine tau A).Additive :=
  associated.additive (Scheme.Spec.obj (op A)) tau

/-- The bounded-below homotopy functor induced by affine association. -/
abbrev associatedAffinePlusMap (tau : StandardTopology) (A : CommRingCat.{u}) :
    HomotopyCategory.Plus (Scheme.QCoh (Scheme.Spec.obj (op A))) ⥤
      HomotopyCategory.Plus (affineAdeq tau A) :=
  (associatedAffine tau A).mapHomotopyCategoryPlus

/-- The bounded-below derived functor induced by affine association. -/
abbrev associatedAffineToBoundedBelowDerived (tau : StandardTopology)
    (A : CommRingCat.{u}) [HasDerivedCategory.{u} (affineAdeq tau A)] :
    HomotopyCategory.Plus (Scheme.QCoh (Scheme.Spec.obj (op A))) ⥤
      DerivedCategory.Plus (affineAdeq tau A) :=
  associatedAffinePlusMap tau A ⋙ DerivedCategory.Plus.Qh

/-- On an affine scheme, association sends exactly the universal
quasi-isomorphisms of bounded-below quasicoherent complexes to
quasi-isomorphisms of adequate complexes. -/
theorem universalQuasiIso_iff_associated (tau : StandardTopology)
    (A : CommRingCat.{u})
    {K L : HomotopyCategory.Plus (Scheme.QCoh (Scheme.Spec.obj (op A)))}
    (g : K ⟶ L) :
    Scheme.QCoh.universalQuasiIso (Scheme.Spec.obj (op A)) g ↔
      HomotopyCategory.Plus.quasiIso (affineAdeq tau A)
        ((associatedAffinePlusMap tau A).map g) :=
  sorry

/-- Association from bounded-below quasicoherent complexes on `Spec A` realizes
the bounded-below derived category of adequate modules as the localization at
universal quasi-isomorphisms. -/
instance associatedPlusIsLocalization (tau : StandardTopology) (A : CommRingCat.{u})
    [HasDerivedCategory.{u} (affineAdeq tau A)] :
    (associatedAffineToBoundedBelowDerived tau A).IsLocalization
      (Scheme.QCoh.universalQuasiIso (Scheme.Spec.obj (op A))) := sorry

end SheafOfModules.Adeq
