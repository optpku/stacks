/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Locality.Criteria
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.EtaleLocal.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ZariskiCover.Basic
public import Mathlib.Data.List.TFAE

/-!
# Pointwise finite type of morphisms of algebraic spaces

A morphism of algebraic spaces is of finite type at a point when it is
locally of finite type after restriction to an open subspace neighbourhood,
and its local finite type property admits equivalent pointwise, base-change,
étale-square, and Zariski-cover characterizations.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism `f : X ⟶ Y` of algebraic spaces is of finite type at a
point `x` of `X` if it is locally of finite type after restriction to
some open subspace neighbourhood of `x`. -/
def FiniteTypeAt {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (x : Points X) : Prop :=
  ∃ (X' : AlgebraicSpace S) (i : X' ⟶ X),
    IsOpenImmersion i ∧ x ∈ Set.range (Points.map i) ∧
      LocallyOfFiniteType (i ≫ f)

/-- Finite type at a point is the existence of an open subspace neighbourhood
on which the morphism is locally of finite type. -/
theorem finiteTypeAt_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (x : Points X) :
    FiniteTypeAt f x ↔
      ∃ (X' : AlgebraicSpace S) (i : X' ⟶ X),
        IsOpenImmersion i ∧ x ∈ Set.range (Points.map i) ∧
          LocallyOfFiniteType (i ≫ f) :=
  Iff.rfl

namespace LocallyOfFiniteType

/-- Every base change of `f` along a morphism from a scheme is locally of
finite type.
Stacks, Tag 040Y (3), `tex/spaces-morphisms.tex:4405–4406`. -/
abbrev baseChangeOnSchemes {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop :=
  Locality.Criteria.forallScheme (@LocallyOfFiniteType S) f

/-- Every base change of `f` along a morphism from an affine scheme is locally
of finite type.
Stacks, Tag 040Y (4), `tex/spaces-morphisms.tex:4407–4408`. -/
abbrev baseChangeOnAffineSchemes {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop :=
  Locality.Criteria.forallAffine (@LocallyOfFiniteType S) f

/-- There is a surjective étale morphism from a scheme to `Y` along which the
base change of `f` is locally of finite type.
Stacks, Tag 040Y (5), `tex/spaces-morphisms.tex:4409–4410`. -/
abbrev existsSurjectiveEtaleTarget {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop :=
  Locality.Criteria.existsSurjectiveEtaleTarget (@LocallyOfFiniteType S) f

/-- There is a surjective étale morphism `φ` from a scheme to `X` such that
`φ ≫ f` is locally of finite type.
Stacks, Tag 040Y (6), `tex/spaces-morphisms.tex:4411–4413`. -/
abbrev existsSurjectiveEtaleSource {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop :=
  Locality.Criteria.existsSurjectiveEtaleSource (@LocallyOfFiniteType S) f

/-- Every étale scheme square over `f` has locally-of-finite-type top arrow.
Stacks, Tag 040Y (7), `tex/spaces-morphisms.tex:4414–4422`. -/
abbrev forallEtaleSquare {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop :=
  Locality.Criteria.forallEtaleSquare (@AlgebraicGeometry.LocallyOfFiniteType) f

/-- There is an étale scheme square over `f` with surjective source cover and
locally-of-finite-type top arrow.
Stacks, Tag 040Y (8), `tex/spaces-morphisms.tex:4423–4431`. -/
abbrev existsEtaleSquare {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop :=
  Locality.Criteria.existsEtaleSquare (@AlgebraicGeometry.LocallyOfFiniteType) f

/-- There are Zariski coverings of `Y` and of the inverse images in `X` on which
the pieces of `f` are locally of finite type.
Stacks, Tag 040Y (9), `tex/spaces-morphisms.tex:4432–4434`. -/
abbrev existsZariskiCover {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop :=
  Locality.Criteria.existsZariskiCover.{u, v} (@LocallyOfFiniteType S) f

end LocallyOfFiniteType

/-- Local finite type of a morphism of algebraic spaces is equivalent to its
pointwise, scheme base-change, affine base-change, étale atlas, étale square,
and Zariski-cover criteria.
Stacks, Tag 040Y, `tex/spaces-morphisms.tex:4398–4461`. -/
theorem locallyOfFiniteType_tfae {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    List.TFAE
      [ LocallyOfFiniteType f
      , ∀ x : Points X, FiniteTypeAt f x
      , LocallyOfFiniteType.baseChangeOnSchemes f
      , LocallyOfFiniteType.baseChangeOnAffineSchemes f
      , LocallyOfFiniteType.existsSurjectiveEtaleTarget f
      , LocallyOfFiniteType.existsSurjectiveEtaleSource f
      , LocallyOfFiniteType.forallEtaleSquare f
      , LocallyOfFiniteType.existsEtaleSquare f
      , LocallyOfFiniteType.existsZariskiCover.{u, v} f ] := by
  have hP : (@LocallyOfFiniteType S : MorphismProperty (AlgebraicSpace S)) =
      etaleLocal (@AlgebraicGeometry.LocallyOfFiniteType) := by
    funext U V g
    exact propext (locallyOfFiniteType_iff g)
  have hlocal := Locality.Criteria.etaleLocal_tfae.{u, v}
    (@AlgebraicGeometry.LocallyOfFiniteType) f
  have hbase : List.TFAE
      [ LocallyOfFiniteType f, LocallyOfFiniteType.baseChangeOnSchemes f
      , LocallyOfFiniteType.baseChangeOnAffineSchemes f
      , LocallyOfFiniteType.existsSurjectiveEtaleTarget f
      , LocallyOfFiniteType.existsSurjectiveEtaleSource f
      , LocallyOfFiniteType.forallEtaleSquare f, LocallyOfFiniteType.existsEtaleSquare f
      , LocallyOfFiniteType.existsZariskiCover.{u, v} f ] := by
    simpa only [LocallyOfFiniteType.baseChangeOnSchemes,
      LocallyOfFiniteType.baseChangeOnAffineSchemes,
      LocallyOfFiniteType.existsSurjectiveEtaleTarget,
      LocallyOfFiniteType.existsSurjectiveEtaleSource, LocallyOfFiniteType.forallEtaleSquare,
      LocallyOfFiniteType.existsEtaleSquare, LocallyOfFiniteType.existsZariskiCover, hP]
      using hlocal
  -- Tag 040Y (1) iff (2), tex/spaces-morphisms.tex:4403–4404,4455–4456.
  have hpoint : LocallyOfFiniteType f ↔ ∀ x : Points X, FiniteTypeAt f x := by sorry
  exact List.tfae_cons_cons.mpr ⟨hpoint,
    List.tfae_cons_cons.mpr ⟨hpoint.symm.trans (hbase.out 0 1),
      (List.tfae_cons_cons.mp hbase).2⟩⟩

namespace LocallyOfFiniteType

/-- A morphism of algebraic spaces is locally of finite type if and only if it is
of finite type at every point. -/
theorem iff_forall_finiteTypeAt {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : LocallyOfFiniteType f ↔ ∀ x : Points X, FiniteTypeAt f x :=
  (locallyOfFiniteType_tfae.{u, u} f).out 0 1

/-- A morphism of algebraic spaces is locally of finite type if and only if every
base change along a scheme is locally of finite type. -/
theorem iff_baseChangeOnSchemes {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : LocallyOfFiniteType f ↔ baseChangeOnSchemes f :=
  (locallyOfFiniteType_tfae.{u, u} f).out 0 2

/-- A morphism of algebraic spaces is locally of finite type if and only if every
base change along an affine scheme is locally of finite type. -/
theorem iff_baseChangeOnAffineSchemes {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : LocallyOfFiniteType f ↔ baseChangeOnAffineSchemes f :=
  (locallyOfFiniteType_tfae.{u, u} f).out 0 3

/-- A morphism of algebraic spaces is locally of finite type if and only if its
base change along some surjective étale scheme atlas of its target is locally of finite type. -/
theorem iff_existsSurjectiveEtaleTarget {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : LocallyOfFiniteType f ↔ existsSurjectiveEtaleTarget f :=
  (locallyOfFiniteType_tfae.{u, u} f).out 0 4

/-- A morphism of algebraic spaces is locally of finite type if and only if its
composite with some surjective étale scheme atlas of its source is locally of finite type. -/
theorem iff_existsSurjectiveEtaleSource {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : LocallyOfFiniteType f ↔ existsSurjectiveEtaleSource f :=
  (locallyOfFiniteType_tfae.{u, u} f).out 0 5

/-- A morphism of algebraic spaces is locally of finite type if and only if every
étale scheme square over it has locally-of-finite-type top arrow. -/
theorem iff_forallEtaleSquare {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : LocallyOfFiniteType f ↔ forallEtaleSquare f :=
  (locallyOfFiniteType_tfae.{u, u} f).out 0 6

/-- A morphism of algebraic spaces is locally of finite type if and only if some
étale scheme square over it has surjective source cover and locally-of-finite-type top arrow. -/
theorem iff_existsEtaleSquare {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : LocallyOfFiniteType f ↔ existsEtaleSquare f :=
  (locallyOfFiniteType_tfae.{u, u} f).out 0 7

/-- A morphism of algebraic spaces is locally of finite type if and only if it is
locally of finite type on Zariski coverings of its target and the full inverse images. -/
theorem iff_existsZariskiCover {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : LocallyOfFiniteType f ↔ existsZariskiCover.{u, v} f :=
  (locallyOfFiniteType_tfae.{u, v} f).out 0 8

end LocallyOfFiniteType

end AlgebraicGeometry.AlgebraicSpace
