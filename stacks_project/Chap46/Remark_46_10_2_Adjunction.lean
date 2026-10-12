/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.DerivedAdeq.Adjunction

open CategoryTheory
open AlgebraicGeometry

#check (AlgebraicGeometry.Scheme.DerivedQCoh.smallPresentation :
  ∀ (S : AlgebraicGeometry.Scheme),
    AlgebraicGeometry.Scheme.DerivedQCoh S ⥤
      AlgebraicGeometry.Scheme.DerivedQCoh.UnliftedSmallZariski S)

#check (SheafOfModules.DerivedAdeq.associated :
  ∀ (S : AlgebraicGeometry.Scheme) (τ : AlgebraicGeometry.StandardTopology),
    AlgebraicGeometry.Scheme.DerivedQCoh S ⥤ SheafOfModules.DerivedAdeq S τ)

#check (SheafOfModules.DerivedAdeq.zariskiRestriction :
  ∀ (S : AlgebraicGeometry.Scheme) (τ : AlgebraicGeometry.StandardTopology),
    SheafOfModules.DerivedAdeq S τ ⥤ AlgebraicGeometry.Scheme.DerivedQCoh S)

#check (SheafOfModules.DerivedAdeq.adjunction :
  ∀ (S : AlgebraicGeometry.Scheme) (τ : AlgebraicGeometry.StandardTopology),
    SheafOfModules.DerivedAdeq.associated S τ ⊣
      SheafOfModules.DerivedAdeq.zariskiRestriction S τ)

#check (SheafOfModules.DerivedAdeq.adjunctionUnitIsIso :
  ∀ (S : AlgebraicGeometry.Scheme) (τ : AlgebraicGeometry.StandardTopology),
    CategoryTheory.IsIso (SheafOfModules.DerivedAdeq.adjunction S τ).unit)
