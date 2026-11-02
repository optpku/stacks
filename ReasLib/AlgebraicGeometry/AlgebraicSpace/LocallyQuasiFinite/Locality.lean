/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ZariskiCover.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Locality.Criteria
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.EtaleLocal.QuasiFinite

/-!
# Locality of quasi-finiteness for algebraic spaces

Local finite type together with local quasi-finiteness can be tested pointwise,
on scheme-valued base changes, on étale atlases, and on Zariski coverings.
The pointwise predicate `QuasiFiniteAt` records only weak local quasi-finiteness,
without a local-finite-type requirement.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism is weakly quasi-finite at a point if its restriction to some
open subspace neighbourhood is locally quasi-finite, without requiring local
finite type. -/
def QuasiFiniteAt {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (x : Points X) : Prop :=
  ∃ (X' : AlgebraicSpace S) (i : X' ⟶ X),
    IsOpenImmersion i ∧ x ∈ Set.range (Points.map i) ∧ LocallyQuasiFinite (i ≫ f)

/-- Weak quasi-finiteness at a point is equivalent to local quasi-finiteness
on an open subspace neighbourhood, without requiring local finite type. -/
theorem quasiFiniteAt_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (x : Points X) :
    QuasiFiniteAt f x ↔
      ∃ (X' : AlgebraicSpace S) (i : X' ⟶ X),
        IsOpenImmersion i ∧ x ∈ Set.range (Points.map i) ∧
          LocallyQuasiFinite (i ≫ f) :=
  Iff.rfl

namespace LocallyQuasiFinite

/-- Every base change along a morphism from a scheme is locally of finite
type and locally quasi-finite. -/
abbrev baseChangeOnSchemes {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop :=
  Locality.Criteria.forallScheme (@LocallyOfFiniteType S ⊓ @LocallyQuasiFinite S) f

/-- Every base change along a morphism from an affine scheme is locally of
finite type and locally quasi-finite. -/
abbrev baseChangeOnAffineSchemes {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop :=
  Locality.Criteria.forallAffine (@LocallyOfFiniteType S ⊓ @LocallyQuasiFinite S) f

/-- There is a surjective étale scheme atlas of the target along which the
base change is locally of finite type and locally quasi-finite. -/
abbrev existsSurjectiveEtaleTarget {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop :=
  Locality.Criteria.existsSurjectiveEtaleTarget
    (@LocallyOfFiniteType S ⊓ @LocallyQuasiFinite S) f

/-- There is a surjective étale scheme atlas of the source whose composite
with the morphism is locally of finite type and locally quasi-finite. -/
abbrev existsSurjectiveEtaleSource {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop :=
  Locality.Criteria.existsSurjectiveEtaleSource
    (@LocallyOfFiniteType S ⊓ @LocallyQuasiFinite S) f

/-- Every commutative scheme square with étale vertical arrows has locally
of finite type and locally quasi-finite top arrow. -/
abbrev forallEtaleSquare {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop :=
  Locality.Criteria.forallEtaleSquare
    (@AlgebraicGeometry.LocallyOfFiniteType ⊓ @AlgebraicGeometry.LocallyQuasiFinite) f

/-- There is a commutative scheme square with étale vertical arrows,
surjective source vertical arrow, and locally of finite type and locally
quasi-finite top arrow. -/
abbrev existsEtaleSquare {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop :=
  Locality.Criteria.existsEtaleSquare
    (@AlgebraicGeometry.LocallyOfFiniteType ⊓ @AlgebraicGeometry.LocallyQuasiFinite) f

/-- There are Zariski coverings of the target and of each inverse image such
that every restricted morphism is locally of finite type and locally
quasi-finite. -/
def existsZariskiCover {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop :=
  ∃ 𝒱 : ZariskiCover.{u, v} Y, ∀ i : 𝒱.I₀,
    ∃ 𝒰 : ZariskiCover.{u, v} (Limits.pullback f (𝒱.f i)), ∀ j : 𝒰.I₀,
      LocallyOfFiniteType (𝒰.f j ≫ Limits.pullback.snd f (𝒱.f i)) ∧
        LocallyQuasiFinite (𝒰.f j ≫ Limits.pullback.snd f (𝒱.f i))

/-- The chosen-pullback and presentation-independent Zariski criteria agree. -/
theorem existsZariskiCover_iff_criteria {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    existsZariskiCover.{u, v} f ↔
      Locality.Criteria.existsZariskiCover.{u, v}
        (@LocallyOfFiniteType S ⊓ @LocallyQuasiFinite S) f := by
  sorry

end LocallyQuasiFinite

/-- For a morphism of algebraic spaces, being locally of finite type and
locally quasi-finite is equivalent to the corresponding condition on an open
neighbourhood of every point, on all scheme or affine scheme base changes,
on a target or source étale atlas, on all or some étale scheme squares, and
on Zariski coverings of the target and its inverse images. -/
theorem locallyQuasiFinite_tfae {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    List.TFAE
      [ LocallyOfFiniteType f ∧ LocallyQuasiFinite f
      , ∀ x : Points X, ∃ (X' : AlgebraicSpace S) (i : X' ⟶ X),
          IsOpenImmersion i ∧ x ∈ Set.range (Points.map i) ∧
            LocallyOfFiniteType (i ≫ f) ∧ LocallyQuasiFinite (i ≫ f)
      , LocallyQuasiFinite.baseChangeOnSchemes f
      , LocallyQuasiFinite.baseChangeOnAffineSchemes f
      , LocallyQuasiFinite.existsSurjectiveEtaleTarget f
      , LocallyQuasiFinite.existsSurjectiveEtaleSource f
      , LocallyQuasiFinite.forallEtaleSquare f
      , LocallyQuasiFinite.existsEtaleSquare f
      , LocallyQuasiFinite.existsZariskiCover.{u, v} f ] :=
  by
    let Q : MorphismProperty Scheme.{u} :=
      @AlgebraicGeometry.LocallyOfFiniteType ⊓ @AlgebraicGeometry.LocallyQuasiFinite
    let P : MorphismProperty (AlgebraicSpace S) :=
      @LocallyOfFiniteType S ⊓ @LocallyQuasiFinite S
    letI : IsEtaleLocalAtSourceAndTarget Q :=
      Scheme.Hom.FiniteType.locallyQuasiFiniteIsEtaleLocalAtSourceAndTarget
    letI : Q.IsStableUnderBaseChange := by
      dsimp [Q]
      infer_instance
    have hP : P = etaleLocal Q := by
      funext U V g
      apply propext
      change (LocallyOfFiniteType g ∧ LocallyQuasiFinite g) ↔ _
      rw [locallyOfFiniteType_iff, locallyQuasiFinite_iff]
      exact ⟨fun h _ _ a b k ha hb w => ⟨h.1 a b k ha hb w, h.2 a b k ha hb w⟩,
        fun h => ⟨fun a b k ha hb w => (h a b k ha hb w).1,
          fun a b k ha hb w => (h a b k ha hb w).2⟩⟩
    have hlocal := Locality.Criteria.etaleLocal_tfae.{u, v} Q f
    have hbase : List.TFAE
        [ LocallyOfFiniteType f ∧ LocallyQuasiFinite f
        , LocallyQuasiFinite.baseChangeOnSchemes f
        , LocallyQuasiFinite.baseChangeOnAffineSchemes f
        , LocallyQuasiFinite.existsSurjectiveEtaleTarget f
        , LocallyQuasiFinite.existsSurjectiveEtaleSource f
        , LocallyQuasiFinite.forallEtaleSquare f
        , LocallyQuasiFinite.existsEtaleSquare f
        , Locality.Criteria.existsZariskiCover.{u, v} P f ] := by
      simpa only [LocallyQuasiFinite.baseChangeOnSchemes,
        LocallyQuasiFinite.baseChangeOnAffineSchemes,
        LocallyQuasiFinite.existsSurjectiveEtaleTarget,
        LocallyQuasiFinite.existsSurjectiveEtaleSource,
        LocallyQuasiFinite.forallEtaleSquare, LocallyQuasiFinite.existsEtaleSquare,
        ← hP, P, Q, MorphismProperty.inf_iff] using hlocal
    have hpoint : (LocallyOfFiniteType f ∧ LocallyQuasiFinite f) ↔
        ∀ x : Points X, ∃ (X' : AlgebraicSpace S) (i : X' ⟶ X),
          IsOpenImmersion i ∧ x ∈ Set.range (Points.map i) ∧
            LocallyOfFiniteType (i ≫ f) ∧ LocallyQuasiFinite (i ≫ f) := by
      sorry
    have hzar := LocallyQuasiFinite.existsZariskiCover_iff_criteria.{u, v} f
    have hbase' : List.TFAE
        [ LocallyOfFiniteType f ∧ LocallyQuasiFinite f
        , LocallyQuasiFinite.baseChangeOnSchemes f
        , LocallyQuasiFinite.baseChangeOnAffineSchemes f
        , LocallyQuasiFinite.existsSurjectiveEtaleTarget f
        , LocallyQuasiFinite.existsSurjectiveEtaleSource f
        , LocallyQuasiFinite.forallEtaleSquare f
        , LocallyQuasiFinite.existsEtaleSquare f
        , LocallyQuasiFinite.existsZariskiCover.{u, v} f ] := by
      simpa only [hzar] using hbase
    exact List.tfae_cons_cons.mpr ⟨hpoint,
      List.tfae_cons_cons.mpr ⟨hpoint.symm.trans (hbase'.out 0 1),
        (List.tfae_cons_cons.mp hbase').2⟩⟩

end AlgebraicGeometry.AlgebraicSpace
