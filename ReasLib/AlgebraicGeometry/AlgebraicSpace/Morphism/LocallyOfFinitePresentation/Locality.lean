/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Locality.Criteria
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.EtaleLocal.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ZariskiCover.Basic

/-!
# Locality of finite presentation for morphisms of algebraic spaces

This file records pointwise, base-change, covering, and étale-square
characterizations of the locally finite presentation property.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism is locally of finite presentation at a point when its restriction
to an open neighbourhood of that point has the property. -/
def FinitePresentationAt {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (x : Points X) : Prop :=
  ∃ (X' : AlgebraicSpace S) (i : X' ⟶ X),
    IsOpenImmersion i ∧ x ∈ Set.range (Points.map i) ∧
      LocallyOfFinitePresentation (i ≫ f)

/-- The pointwise property unfolds to an open neighbourhood with locally finite
presentation restriction. -/
theorem finitePresentationAt_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (x : Points X) :
    FinitePresentationAt f x ↔
      ∃ (X' : AlgebraicSpace S) (i : X' ⟶ X),
        IsOpenImmersion i ∧ x ∈ Set.range (Points.map i) ∧
          LocallyOfFinitePresentation (i ≫ f) :=
  Iff.rfl

namespace LocallyOfFinitePresentation

/-- Every base change along a morphism from a scheme is locally of finite
presentation. -/
abbrev baseChangeOnSchemes {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop :=
  Locality.Criteria.forallScheme (@LocallyOfFinitePresentation S) f

/-- Every base change along a morphism from an affine scheme is locally of finite
presentation. -/
abbrev baseChangeOnAffineSchemes {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop :=
  Locality.Criteria.forallAffine (@LocallyOfFinitePresentation S) f

/-- A surjective étale scheme cover of the target makes the base change locally
of finite presentation. -/
abbrev existsSurjectiveEtaleTarget {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop :=
  Locality.Criteria.existsSurjectiveEtaleTarget (@LocallyOfFinitePresentation S) f

/-- A surjective étale scheme cover of the source has locally finite presentation
composite with the given morphism. -/
abbrev existsSurjectiveEtaleSource {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop :=
  Locality.Criteria.existsSurjectiveEtaleSource (@LocallyOfFinitePresentation S) f

/-- Every commutative étale scheme square over the morphism has locally finite
presentation top arrow. -/
abbrev forallEtaleSquare {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop :=
  Locality.Criteria.forallEtaleSquare (@AlgebraicGeometry.LocallyOfFinitePresentation) f

/-- There is a commutative étale scheme square over the morphism whose source
vertical map is surjective and whose top arrow is locally of finite
presentation. -/
abbrev existsEtaleSquare {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop :=
  Locality.Criteria.existsEtaleSquare (@AlgebraicGeometry.LocallyOfFinitePresentation) f

/-- There are Zariski coverings of the target and its full inverse images on
which the restricted morphisms are locally of finite presentation. -/
abbrev existsZariskiCover {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop :=
  Locality.Criteria.existsZariskiCover.{u, v} (@LocallyOfFinitePresentation S) f

end LocallyOfFinitePresentation

/-- The nine standard locality conditions for local finite presentation are
equivalent. -/
theorem locallyOfFinitePresentation_tfae {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    List.TFAE
      [ LocallyOfFinitePresentation f
      , ∀ x : Points X, FinitePresentationAt f x
      , LocallyOfFinitePresentation.baseChangeOnSchemes f
      , LocallyOfFinitePresentation.baseChangeOnAffineSchemes f
      , LocallyOfFinitePresentation.existsSurjectiveEtaleTarget f
      , LocallyOfFinitePresentation.existsSurjectiveEtaleSource f
      , LocallyOfFinitePresentation.forallEtaleSquare f
      , LocallyOfFinitePresentation.existsEtaleSquare f
      , LocallyOfFinitePresentation.existsZariskiCover.{u, v} f ] :=
  by
    have hP : (@LocallyOfFinitePresentation S : MorphismProperty (AlgebraicSpace S)) =
        etaleLocal (@AlgebraicGeometry.LocallyOfFinitePresentation) := by
      funext U V g
      exact propext (locallyOfFinitePresentation_iff g)
    have hlocal := Locality.Criteria.etaleLocal_tfae.{u, v}
      (@AlgebraicGeometry.LocallyOfFinitePresentation) f
    have hbase : List.TFAE
        [ LocallyOfFinitePresentation f, LocallyOfFinitePresentation.baseChangeOnSchemes f
        , LocallyOfFinitePresentation.baseChangeOnAffineSchemes f
        , LocallyOfFinitePresentation.existsSurjectiveEtaleTarget f
        , LocallyOfFinitePresentation.existsSurjectiveEtaleSource f
        , LocallyOfFinitePresentation.forallEtaleSquare f
        , LocallyOfFinitePresentation.existsEtaleSquare f
        , LocallyOfFinitePresentation.existsZariskiCover.{u, v} f ] := by
      simpa only [LocallyOfFinitePresentation.baseChangeOnSchemes,
        LocallyOfFinitePresentation.baseChangeOnAffineSchemes,
        LocallyOfFinitePresentation.existsSurjectiveEtaleTarget,
        LocallyOfFinitePresentation.existsSurjectiveEtaleSource,
        LocallyOfFinitePresentation.forallEtaleSquare,
        LocallyOfFinitePresentation.existsEtaleSquare,
        LocallyOfFinitePresentation.existsZariskiCover, hP] using hlocal
    have hpoint : LocallyOfFinitePresentation f ↔ ∀ x : Points X, FinitePresentationAt f x := by
      sorry
    exact List.tfae_cons_cons.mpr ⟨hpoint,
      List.tfae_cons_cons.mpr ⟨hpoint.symm.trans (hbase.out 0 1),
        (List.tfae_cons_cons.mp hbase).2⟩⟩

end AlgebraicGeometry.AlgebraicSpace
