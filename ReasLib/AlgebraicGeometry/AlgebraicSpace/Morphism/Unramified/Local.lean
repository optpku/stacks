/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Unramified
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Locality.Criteria
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.EtaleLocal.Unramified
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ZariskiCover.Basic

/-!
# Local characterizations of unramified morphisms of algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism `f : X ⟶ Y` of algebraic spaces is unramified at a point `x` of
`X` if it is unramified after restriction to some open subspace neighbourhood
of `x`. -/
def UnramifiedAt {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (x : Points X) : Prop :=
  ∃ (X' : AlgebraicSpace S) (i : X' ⟶ X),
    IsOpenImmersion i ∧ x ∈ Set.range (Points.map i) ∧ Unramified (i ≫ f)

/-- Unramifiedness at a point is the existence of an open subspace neighbourhood
on which the morphism is unramified. -/
theorem unramifiedAt_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (x : Points X) :
    UnramifiedAt f x ↔
      ∃ (X' : AlgebraicSpace S) (i : X' ⟶ X),
        IsOpenImmersion i ∧ x ∈ Set.range (Points.map i) ∧ Unramified (i ≫ f) :=
  Iff.rfl

namespace Unramified

/-- Every base change of `f` along a morphism from a scheme is unramified. -/
abbrev baseChangeOnSchemes {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop :=
  Locality.Criteria.forallScheme (@Unramified S) f

/-- Every base change of `f` along a morphism from an affine scheme is
unramified. -/
abbrev baseChangeOnAffineSchemes {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop :=
  Locality.Criteria.forallAffine (@Unramified S) f

/-- There is a surjective étale morphism from a scheme to `Y` along which the
base change of `f` is unramified. -/
abbrev existsSurjectiveEtaleTarget {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop :=
  Locality.Criteria.existsSurjectiveEtaleTarget (@Unramified S) f

/-- There is a surjective étale morphism `φ` from a scheme to `X` such that
`φ ≫ f` is unramified. -/
abbrev existsSurjectiveEtaleSource {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop :=
  Locality.Criteria.existsSurjectiveEtaleSource (@Unramified S) f

/-- Every étale scheme square over `f` has unramified top arrow. -/
abbrev forallEtaleSquare {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop :=
  Locality.Criteria.forallEtaleSquare (@AlgebraicGeometry.Unramified) f

/-- There is an étale scheme square over `f` with surjective source cover and
unramified top arrow. -/
abbrev existsEtaleSquare {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop :=
  Locality.Criteria.existsEtaleSquare (@AlgebraicGeometry.Unramified) f

/-- There are Zariski coverings of `Y` and of the inverse images in `X` on which
the pieces of `f` are unramified. -/
abbrev existsZariskiCover {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop :=
  Locality.Criteria.existsZariskiCover.{u, v} (@Unramified S) f

end Unramified

/-- Unramifiedness of a morphism of algebraic spaces is equivalent to pointwise
unramifiedness, unramifiedness after scheme or affine-scheme base change,
unramifiedness on surjective étale target or source covers, the universal or
existential étale scheme-square criterion, and unramifiedness on Zariski covers
of the target and its inverse images. -/
theorem unramified_tfae {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    List.TFAE
      [ Unramified f
      , ∀ x : Points X, UnramifiedAt f x
      , Unramified.baseChangeOnSchemes f
      , Unramified.baseChangeOnAffineSchemes f
      , Unramified.existsSurjectiveEtaleTarget f
      , Unramified.existsSurjectiveEtaleSource f
      , Unramified.forallEtaleSquare f
      , Unramified.existsEtaleSquare f
      , Unramified.existsZariskiCover.{u, v} f ] :=
  by
    have hP : (@Unramified S : MorphismProperty (AlgebraicSpace S)) =
        etaleLocal (@AlgebraicGeometry.Unramified) := by
      funext U V g
      exact propext (unramified_iff g)
    have hlocal := Locality.Criteria.etaleLocal_tfae.{u, v}
      (@AlgebraicGeometry.Unramified) f
    have hbase : List.TFAE
        [ Unramified f, Unramified.baseChangeOnSchemes f
        , Unramified.baseChangeOnAffineSchemes f
        , Unramified.existsSurjectiveEtaleTarget f
        , Unramified.existsSurjectiveEtaleSource f
        , Unramified.forallEtaleSquare f, Unramified.existsEtaleSquare f
        , Unramified.existsZariskiCover.{u, v} f ] := by
      simpa only [Unramified.baseChangeOnSchemes, Unramified.baseChangeOnAffineSchemes,
        Unramified.existsSurjectiveEtaleTarget, Unramified.existsSurjectiveEtaleSource,
        Unramified.forallEtaleSquare, Unramified.existsEtaleSquare,
        Unramified.existsZariskiCover, hP] using hlocal
    have hpoint : Unramified f ↔ ∀ x : Points X, UnramifiedAt f x := by sorry
    exact List.tfae_cons_cons.mpr ⟨hpoint,
      List.tfae_cons_cons.mpr ⟨hpoint.symm.trans (hbase.out 0 1),
        (List.tfae_cons_cons.mp hbase).2⟩⟩


end AlgebraicGeometry.AlgebraicSpace
