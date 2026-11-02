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
def baseChangeOnSchemes {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop :=
  ∀ {Z : Over S} (g : ofOver Z ⟶ Y),
    LocallyOfFiniteType (pullbackAlongScheme.snd f g) ∧
      LocallyQuasiFinite (pullbackAlongScheme.snd f g)

/-- Every base change along a morphism from an affine scheme is locally of
finite type and locally quasi-finite. -/
def baseChangeOnAffineSchemes {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop :=
  ∀ {Z : Over S} (g : ofOver Z ⟶ Y),
    IsAffine Z.left → LocallyOfFiniteType (pullbackAlongScheme.snd f g) ∧
      LocallyQuasiFinite (pullbackAlongScheme.snd f g)

/-- There is a surjective étale scheme atlas of the target along which the
base change is locally of finite type and locally quasi-finite. -/
def existsSurjectiveEtaleTarget {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop :=
  ∃ (V : Over S) (b : ofOver V ⟶ Y),
    (over (@AlgebraicGeometry.Etale)).presheaf b ∧
      Surjective b ∧ LocallyOfFiniteType (pullbackAlongScheme.snd f b) ∧
        LocallyQuasiFinite (pullbackAlongScheme.snd f b)

/-- There is a surjective étale scheme atlas of the source whose composite
with the morphism is locally of finite type and locally quasi-finite. -/
def existsSurjectiveEtaleSource {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop :=
  ∃ (U : Over S) (φ : ofOver U ⟶ X),
    (over (@AlgebraicGeometry.Etale)).presheaf φ ∧
      Surjective φ ∧ LocallyOfFiniteType (φ ≫ f) ∧ LocallyQuasiFinite (φ ≫ f)

/-- Every commutative scheme square with étale vertical arrows has locally
of finite type and locally quasi-finite top arrow. -/
def forallEtaleSquare {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop :=
  ∀ {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
    (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V),
    (over (@AlgebraicGeometry.Etale)).presheaf a →
      (over (@AlgebraicGeometry.Etale)).presheaf b →
        a ≫ f = yoneda.map h ≫ b →
          AlgebraicGeometry.LocallyOfFiniteType h.left ∧
            AlgebraicGeometry.LocallyQuasiFinite h.left

/-- There is a commutative scheme square with étale vertical arrows,
surjective source vertical arrow, and locally of finite type and locally
quasi-finite top arrow. -/
def existsEtaleSquare {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop :=
  ∃ (U V : Over S) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V),
    (over (@AlgebraicGeometry.Etale)).presheaf a ∧
      (over (@AlgebraicGeometry.Etale)).presheaf b ∧
        a ≫ f = ofOverMap h ≫ b ∧
          Surjective a ∧ AlgebraicGeometry.LocallyOfFiniteType h.left ∧
            AlgebraicGeometry.LocallyQuasiFinite h.left

/-- There are Zariski coverings of the target and of each inverse image such
that every restricted morphism is locally of finite type and locally
quasi-finite. -/
def existsZariskiCover {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop :=
  ∃ 𝒱 : ZariskiCover.{u, v} Y, ∀ i : 𝒱.I₀,
    ∃ 𝒰 : ZariskiCover.{u, v} (Limits.pullback f (𝒱.f i)), ∀ j : 𝒰.I₀,
      LocallyOfFiniteType (𝒰.f j ≫ Limits.pullback.snd f (𝒱.f i)) ∧
        LocallyQuasiFinite (𝒰.f j ≫ Limits.pullback.snd f (𝒱.f i))

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
  sorry

end AlgebraicGeometry.AlgebraicSpace
