/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Germ.Category

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Germ.Hom

/-! ## Scheme-level base changes

In the definition preceding Stacks Tag 02YF, the fibre products are formed in the category of
schemes.  A germ morphism is only represented on a neighbourhood, so the representatives of the
source and
base maps are part of the data.  The point of the scheme-theoretic pullback is also part of the
data: a pair of points of a fibre product does not determine a point without choosing a prime of
the tensor product of residue fields.  The two base representatives may use different open
neighbourhoods of the same distinguished point; their projections still land in the same base
germ.  Shrinking any representative is permitted by the equality with its given germ morphism.
-/

/-- A scheme-theoretic pullback of two represented germ morphisms, together with the point used
to form its germ.

The fields `sourceRepresentative` and `baseRepresentative` anchor the construction to the
given germ morphisms.  The pullback object is the canonical Scheme pullback of these actual
scheme morphisms, while `point` records the choice allowed in the Stacks definition. -/
structure SchemePullbackGerm {X S B : Germ.{u}} (f : X ⟶ S) (g : B ⟶ S) where
  /-- A representative of the source germ morphism. -/
  sourceRepresentative : Representative X S
  /-- The source representative represents `f`. -/
  sourceRepresentative_eq : mk sourceRepresentative = f
  /-- A representative of the base germ morphism. -/
  baseRepresentative : Representative B S
  /-- The base representative represents `g`. -/
  baseRepresentative_eq : mk baseRepresentative = g
  /-- The chosen point of the scheme-theoretic fibre product. -/
  point : pullback (C := Scheme) baseRepresentative.hom sourceRepresentative.hom
  /-- The chosen point lies over the distinguished point of `B`. -/
  point_base :
    pullback.fst (C := Scheme) baseRepresentative.hom sourceRepresentative.hom point =
      B.pointIn baseRepresentative.neighborhood baseRepresentative.mem_neighborhood
  /-- The chosen point lies over the distinguished point of `X`. -/
  point_source :
    pullback.snd (C := Scheme) baseRepresentative.hom sourceRepresentative.hom point =
      X.pointIn sourceRepresentative.neighborhood sourceRepresentative.mem_neighborhood

namespace SchemePullbackGerm

/-- The canonical Scheme pullback square behind a `SchemePullbackGerm`. -/
theorem isPullback {X S B : Germ.{u}} {f : X ⟶ S} {g : B ⟶ S}
    (p : SchemePullbackGerm f g) :
    IsPullback (pullback.fst (C := Scheme) p.baseRepresentative.hom p.sourceRepresentative.hom)
      (pullback.snd (C := Scheme) p.baseRepresentative.hom p.sourceRepresentative.hom)
      p.baseRepresentative.hom p.sourceRepresentative.hom :=
  IsPullback.of_hasPullback _ _

/-- The germ at the selected point of the scheme-theoretic pullback. -/
def germ {X S B : Germ.{u}} {f : X ⟶ S} {g : B ⟶ S}
    (p : SchemePullbackGerm f g) : Germ :=
  Germ.of (pullback (C := Scheme) p.baseRepresentative.hom p.sourceRepresentative.hom) p.point

/-- The selected pullback germ has the canonical Scheme pullback as its underlying scheme. -/
@[simp] theorem germ_scheme {X S B : Germ.{u}} {f : X ⟶ S} {g : B ⟶ S}
    (p : SchemePullbackGerm f g) :
    p.germ.scheme = pullback (C := Scheme) p.baseRepresentative.hom
      p.sourceRepresentative.hom := rfl

/-- The distinguished point of the pullback germ is the specified pullback point. -/
@[simp] theorem germ_point {X S B : Germ.{u}} {f : X ⟶ S} {g : B ⟶ S}
    (p : SchemePullbackGerm f g) : p.germ.point = p.point := rfl

/-- The first projection and neighbourhood inclusion preserve the chosen base point. -/
theorem toBase_mapPoint {X S B : Germ.{u}} {f : X ⟶ S} {g : B ⟶ S}
    (p : SchemePullbackGerm f g) :
    (pullback.fst (C := Scheme) p.baseRepresentative.hom p.sourceRepresentative.hom ≫
      p.baseRepresentative.neighborhood.ι) p.point = B.point := by
  rw [Scheme.Hom.comp_apply, p.point_base, Germ.pointIn_val]

/-- The second projection and neighbourhood inclusion preserve the chosen source point. -/
theorem toSource_mapPoint {X S B : Germ.{u}} {f : X ⟶ S} {g : B ⟶ S}
    (p : SchemePullbackGerm f g) :
    (pullback.snd (C := Scheme) p.baseRepresentative.hom p.sourceRepresentative.hom ≫
      p.sourceRepresentative.neighborhood.ι) p.point = X.point := by
  rw [Scheme.Hom.comp_apply, p.point_source, Germ.pointIn_val]

/-- The selected pullback germ maps to the common base germ. -/
def toBase {X S B : Germ.{u}} {f : X ⟶ S} {g : B ⟶ S}
    (p : SchemePullbackGerm f g) : germ p ⟶ B :=
  Germ.Hom.ofGlobal
    (pullback.fst (C := Scheme) p.baseRepresentative.hom p.sourceRepresentative.hom ≫
      p.baseRepresentative.neighborhood.ι)
    p.toBase_mapPoint

/-- The selected pullback germ maps to the source germ. -/
def toSource {X S B : Germ.{u}} {f : X ⟶ S} {g : B ⟶ S}
    (p : SchemePullbackGerm f g) : germ p ⟶ X :=
  Germ.Hom.ofGlobal
    (pullback.snd (C := Scheme) p.baseRepresentative.hom p.sourceRepresentative.hom ≫
      p.sourceRepresentative.neighborhood.ι)
    p.toSource_mapPoint

end SchemePullbackGerm

/-- A chosen comparison of two germ morphisms after scheme-theoretic base changes satisfying
`Q`.  The two pullbacks use actual neighbourhood representatives and selected points, as in
Stacks, and the comparison is an isomorphism of the resulting germs over the common base. -/
structure BaseLocalIso (Q : MorphismProperty Germ.{u}) {X S X' S' : Germ.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') where
  /-- The common germ over which the two presentations are compared. -/
  base : Germ.{u}
  /-- The left base-change morphism of germs. -/
  leftBase : base ⟶ S
  /-- The left base-change morphism satisfies `Q`. -/
  leftBaseProperty : Q leftBase
  /-- The right base-change morphism of germs. -/
  rightBase : base ⟶ S'
  /-- The right base-change morphism satisfies `Q`. -/
  rightBaseProperty : Q rightBase
  /-- The left scheme-theoretic pullback and its selected point. -/
  leftChange : SchemePullbackGerm f leftBase
  /-- The right scheme-theoretic pullback and its selected point. -/
  rightChange : SchemePullbackGerm f' rightBase
  /-- The selected pullback germs are isomorphic over the common base. -/
  comparison : Over.mk leftChange.toBase ≅ Over.mk rightChange.toBase

namespace BaseLocalIso

/-- The selected left pullback germ. -/
def left {Q : MorphismProperty Germ.{u}} {X S X' S' : Germ.{u}}
    {f : X ⟶ S} {f' : X' ⟶ S'} (e : BaseLocalIso Q f f') : Germ :=
  e.leftChange.germ

/-- The selected right pullback germ. -/
def right {Q : MorphismProperty Germ.{u}} {X S X' S' : Germ.{u}}
    {f : X ⟶ S} {f' : X' ⟶ S'} (e : BaseLocalIso Q f f') : Germ :=
  e.rightChange.germ

/-- The left pullback projection to the source germ. -/
def leftToSource {Q : MorphismProperty Germ.{u}} {X S X' S' : Germ.{u}}
    {f : X ⟶ S} {f' : X' ⟶ S'} (e : BaseLocalIso Q f f') : e.left ⟶ X :=
  e.leftChange.toSource

/-- The left pullback projection to the common base germ. -/
def leftToBase {Q : MorphismProperty Germ.{u}} {X S X' S' : Germ.{u}}
    {f : X ⟶ S} {f' : X' ⟶ S'} (e : BaseLocalIso Q f f') : e.left ⟶ e.base :=
  e.leftChange.toBase

/-- The right pullback projection to the source germ. -/
def rightToSource {Q : MorphismProperty Germ.{u}} {X S X' S' : Germ.{u}}
    {f : X ⟶ S} {f' : X' ⟶ S'} (e : BaseLocalIso Q f f') : e.right ⟶ X' :=
  e.rightChange.toSource

/-- The right pullback projection to the common base germ. -/
def rightToBase {Q : MorphismProperty Germ.{u}} {X S X' S' : Germ.{u}}
    {f : X ⟶ S} {f' : X' ⟶ S'} (e : BaseLocalIso Q f f') : e.right ⟶ e.base :=
  e.rightChange.toBase

/-- The left Scheme-level pullback square used by the witness. -/
theorem leftIsPullback {Q : MorphismProperty Germ.{u}} {X S X' S' : Germ.{u}}
    {f : X ⟶ S} {f' : X' ⟶ S'} (e : BaseLocalIso Q f f') :
    IsPullback
      (pullback.fst (C := Scheme) e.leftChange.baseRepresentative.hom
        e.leftChange.sourceRepresentative.hom)
      (pullback.snd (C := Scheme) e.leftChange.baseRepresentative.hom
        e.leftChange.sourceRepresentative.hom)
      e.leftChange.baseRepresentative.hom e.leftChange.sourceRepresentative.hom :=
  e.leftChange.isPullback

/-- The right Scheme-level pullback square used by the witness. -/
theorem rightIsPullback {Q : MorphismProperty Germ.{u}} {X S X' S' : Germ.{u}}
    {f : X ⟶ S} {f' : X' ⟶ S'} (e : BaseLocalIso Q f f') :
    IsPullback
      (pullback.fst (C := Scheme) e.rightChange.baseRepresentative.hom
        e.rightChange.sourceRepresentative.hom)
      (pullback.snd (C := Scheme) e.rightChange.baseRepresentative.hom
        e.rightChange.sourceRepresentative.hom)
      e.rightChange.baseRepresentative.hom e.rightChange.sourceRepresentative.hom :=
  e.rightChange.isPullback

/-- Reverse a chosen local-on-the-base comparison. -/
def symm {Q : MorphismProperty Germ.{u}} {X S X' S' : Germ.{u}}
    {f : X ⟶ S} {f' : X' ⟶ S'} (e : BaseLocalIso Q f f') :
    BaseLocalIso Q f' f where
  base := e.base
  leftBase := e.rightBase
  leftBaseProperty := e.rightBaseProperty
  rightBase := e.leftBase
  rightBaseProperty := e.leftBaseProperty
  leftChange := e.rightChange
  rightChange := e.leftChange
  comparison := e.comparison.symm

/-- The defining representative, Scheme-pullback, and base-property conditions
of a chosen comparison. -/
theorem spec {Q : MorphismProperty Germ.{u}} {X S X' S' : Germ.{u}}
    {f : X ⟶ S} {f' : X' ⟶ S'} (e : BaseLocalIso Q f f') :
    Q e.leftBase ∧ Q e.rightBase ∧
      Germ.Hom.mk e.leftChange.sourceRepresentative = f ∧
      Germ.Hom.mk e.leftChange.baseRepresentative = e.leftBase ∧
      Germ.Hom.mk e.rightChange.sourceRepresentative = f' ∧
      Germ.Hom.mk e.rightChange.baseRepresentative = e.rightBase ∧
      IsPullback
        (pullback.fst (C := Scheme) e.leftChange.baseRepresentative.hom
          e.leftChange.sourceRepresentative.hom)
        (pullback.snd (C := Scheme) e.leftChange.baseRepresentative.hom
          e.leftChange.sourceRepresentative.hom)
        e.leftChange.baseRepresentative.hom e.leftChange.sourceRepresentative.hom ∧
      IsPullback
        (pullback.fst (C := Scheme) e.rightChange.baseRepresentative.hom
          e.rightChange.sourceRepresentative.hom)
        (pullback.snd (C := Scheme) e.rightChange.baseRepresentative.hom
          e.rightChange.sourceRepresentative.hom)
        e.rightChange.baseRepresentative.hom e.rightChange.sourceRepresentative.hom := by
  exact ⟨e.leftBaseProperty, e.rightBaseProperty,
    e.leftChange.sourceRepresentative_eq, e.leftChange.baseRepresentative_eq,
    e.rightChange.sourceRepresentative_eq, e.rightChange.baseRepresentative_eq,
    e.leftChange.isPullback, e.rightChange.isPullback⟩

end BaseLocalIso

/-- Two germ morphisms are locally on the base isomorphic with respect to `Q` when a
chosen comparison exists. -/
def IsLocallyOnBaseIsomorphic (Q : MorphismProperty Germ.{u})
    {X S X' S' : Germ.{u}} (f : X ⟶ S) (f' : X' ⟶ S') : Prop :=
  Nonempty (BaseLocalIso Q f f')

/-- A chosen local-on-the-base comparison yields local isomorphism on the base. -/
theorem BaseLocalIso.isLocallyOnBaseIsomorphic {Q : MorphismProperty Germ.{u}}
    {X S X' S' : Germ.{u}} {f : X ⟶ S} {f' : X' ⟶ S'}
    (e : BaseLocalIso Q f f') : IsLocallyOnBaseIsomorphic Q f f' :=
  ⟨e⟩

namespace IsLocallyOnBaseIsomorphic

/-- Local isomorphism on the base provides a comparison with its defining representative,
Scheme-pullback, and base-property conditions.  The point conditions are the projections
`SchemePullbackGerm.point_base` and `SchemePullbackGerm.point_source`. -/
theorem exists_spec {Q : MorphismProperty Germ.{u}} {X S X' S' : Germ.{u}}
    {f : X ⟶ S} {f' : X' ⟶ S'} (h : IsLocallyOnBaseIsomorphic Q f f') :
    ∃ e : BaseLocalIso Q f f',
      Q e.leftBase ∧ Q e.rightBase ∧
        Germ.Hom.mk e.leftChange.sourceRepresentative = f ∧
        Germ.Hom.mk e.leftChange.baseRepresentative = e.leftBase ∧
        Germ.Hom.mk e.rightChange.sourceRepresentative = f' ∧
        Germ.Hom.mk e.rightChange.baseRepresentative = e.rightBase ∧
        IsPullback
          (pullback.fst (C := Scheme) e.leftChange.baseRepresentative.hom
            e.leftChange.sourceRepresentative.hom)
          (pullback.snd (C := Scheme) e.leftChange.baseRepresentative.hom
            e.leftChange.sourceRepresentative.hom)
          e.leftChange.baseRepresentative.hom e.leftChange.sourceRepresentative.hom ∧
        IsPullback
          (pullback.fst (C := Scheme) e.rightChange.baseRepresentative.hom
            e.rightChange.sourceRepresentative.hom)
          (pullback.snd (C := Scheme) e.rightChange.baseRepresentative.hom
            e.rightChange.sourceRepresentative.hom)
          e.rightChange.baseRepresentative.hom e.rightChange.sourceRepresentative.hom := by
  rcases h with ⟨e⟩
  exact ⟨e, e.spec⟩

/-- Local isomorphism on the base is symmetric. -/
theorem symm {Q : MorphismProperty Germ.{u}} {X S X' S' : Germ.{u}}
    {f : X ⟶ S} {f' : X' ⟶ S'} (h : IsLocallyOnBaseIsomorphic Q f f') :
    IsLocallyOnBaseIsomorphic Q f' f := by
  rcases h with ⟨e⟩
  exact ⟨e.symm⟩

end IsLocallyOnBaseIsomorphic

end AlgebraicGeometry.Scheme.Germ.Hom
