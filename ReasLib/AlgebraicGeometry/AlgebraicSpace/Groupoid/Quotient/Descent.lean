/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.DescentDatum

/-!
# Explicit descent for quotient stacks

Local atlas presentations and their overlap arrows describe fibre objects and
fibre morphisms of the fppf quotient stack, compatibly with refinements.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits Opposite
open Functor
open CategoryTheory.CategoryOfElements

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- The overlap arrow `r` realises the canonical composite of the given fibre isomorphisms as
`π(r)`, after the source and target laws. -/
def IsPiArrow {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {T : Over S} {ι : Type u} (family : ι → Over T.left)
    (x : (fppfQuotientStack G).p.Fiber T)
    (u : ∀ i, ofOver (coverOver family i) ⟶ G.U.left)
    (e : ∀ i, atlasObj G (u i) ≅ Chosen.reindexObj (fppfQuotientStack G).p (coverHom family i) x)
    {i j : ι} (r : ofOver (pairOver family i j) ⟶ G.R.left) : Prop :=
  ∃ (hs : r ≫ G.s.left = ofOverMap (pr0 family i j) ≫ u i)
    (ht : r ≫ G.t.left = ofOverMap (pr1 family i j) ≫ u j),
    (sourceComparison G family (u i) hs).hom ≫
        Chosen.reindexMap (fppfQuotientStack G).p (pr0 family i j) (e i).hom ≫
        (overlapAssociator G family x i j).hom ≫
        Chosen.reindexMap (fppfQuotientStack G).p (pr1 family i j) (e j).inv ≫
        (overlapTargetComparison G family (u j) ht).inv =
      atlasArrow G r

/-- `IsPiArrow` records the source and target laws together with equality of `atlasArrow r`
against the named canonical composite. -/
theorem isPiArrow_spec {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {T : Over S} {ι : Type u} (family : ι → Over T.left)
    (x : (fppfQuotientStack G).p.Fiber T)
    (u : ∀ i, ofOver (coverOver family i) ⟶ G.U.left)
    (e : ∀ i, atlasObj G (u i) ≅ Chosen.reindexObj (fppfQuotientStack G).p (coverHom family i) x)
    {i j : ι} (r : ofOver (pairOver family i j) ⟶ G.R.left) :
    IsPiArrow G family x u e (i := i) (j := j) r ↔
      ∃ (hs : r ≫ G.s.left = ofOverMap (pr0 family i j) ≫ u i)
        (ht : r ≫ G.t.left = ofOverMap (pr1 family i j) ≫ u j),
        (sourceComparison G family (u i) hs).hom ≫
            Chosen.reindexMap (fppfQuotientStack G).p (pr0 family i j) (e i).hom ≫
            (overlapAssociator G family x i j).hom ≫
            Chosen.reindexMap (fppfQuotientStack G).p (pr1 family i j) (e j).inv ≫
            (overlapTargetComparison G family (u j) ht).inv =
          atlasArrow G r := by
  unfold IsPiArrow
  with_reducible exact Iff.rfl

/-- An object of `[U/R]_T` corresponds to a `[U/R]`-descent datum when each restriction is
`π(u_i)` via chosen fibre isomorphisms and each overlap isomorphism is `π(r_ij)`. -/
structure Corresponds {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {T : Over S} {ι : Type u} (family : ι → Over T.left)
    (x : (fppfQuotientStack G).p.Fiber T) (D : DescentDatum G family) where
  /-- The fibre isomorphisms `π(u_i) ≅ f_i^* x`. -/
  e : ∀ i, atlasObj G (D.u i) ≅ Chosen.reindexObj (fppfQuotientStack G).p (coverHom family i) x
  /-- Each overlap arrow realises the named canonical composite as `π(r_ij)`. -/
  overlap : ∀ i j, IsPiArrow G family x D.u e (D.r i j)

namespace Corresponds

/-- A correspondence supplies fibre isomorphisms realising each overlap arrow as `π(r_ij)`. -/
theorem spec {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {ι : Type u} {family : ι → Over T.left}
    {x : (fppfQuotientStack G).p.Fiber T} {D : DescentDatum G family}
    (h : Corresponds G family x D) :
    ∀ i j, IsPiArrow G family x D.u h.e (D.r i j) :=
  h.overlap

/-- Reindexing the local presentation isomorphisms preserves the specified overlap arrows. -/
theorem pullback_overlap {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {ι : Type u} {family : ι → Over T.left}
    {x : (fppfQuotientStack G).p.Fiber T} {D : DescentDatum G family}
    (h : Corresponds G family x D) {ι' : Type u} {family' : ι' → Over T.left}
    (α : ι' → ι) (φ : ∀ j, family' j ⟶ family (α j)) :
    let e : ∀ j, atlasObj G ((D.pullback α φ).u j) ≅
        Chosen.reindexObj (fppfQuotientStack G).p (coverHom family' j) x :=
      fun j ↦
        atlasObjReindexIso G (DescentDatum.coverMap α φ j) (D.u (α j)) ≪≫
          (Chosen.reindex (fppfQuotientStack G).p (DescentDatum.coverMap α φ j)).mapIso (h.e (α j)) ≪≫
          (Chosen.Reindex.specifiedCompIsoApp (fppfQuotientStack G).p
              (coverHom family (α j)) (DescentDatum.coverMap α φ j)
              (DescentDatum.coverMap α φ j ≫ coverHom family (α j)) rfl x).symm ≪≫
          Chosen.Reindex.congrIsoApp (fppfQuotientStack G).p
            (DescentDatum.coverMap_coverHom α φ j) x
    ∀ i j, IsPiArrow G family' x (D.pullback α φ).u e ((D.pullback α φ).r i j) := sorry

/-- Pull a correspondence back along a refinement of indexed families. -/
def pullback {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {ι : Type u} {family : ι → Over T.left}
    {x : (fppfQuotientStack G).p.Fiber T} {D : DescentDatum G family}
    (h : Corresponds G family x D) {ι' : Type u} {family' : ι' → Over T.left}
    (α : ι' → ι) (φ : ∀ j, family' j ⟶ family (α j)) :
    Corresponds G family' x (D.pullback α φ) where
  e := fun j ↦
    atlasObjReindexIso G (DescentDatum.coverMap α φ j) (D.u (α j)) ≪≫
      (Chosen.reindex (fppfQuotientStack G).p (DescentDatum.coverMap α φ j)).mapIso (h.e (α j)) ≪≫
      (Chosen.Reindex.specifiedCompIsoApp (fppfQuotientStack G).p
          (coverHom family (α j)) (DescentDatum.coverMap α φ j)
          (DescentDatum.coverMap α φ j ≫ coverHom family (α j)) rfl x).symm ≪≫
      Chosen.Reindex.congrIsoApp (fppfQuotientStack G).p
        (DescentDatum.coverMap_coverHom α φ j) x
  overlap := pullback_overlap h α φ

set_option maxHeartbeats 800000 in
/-- The pulled-back fibre isomorphism at `j` is the reindexing of `h.e (α j)` along `φ_j`. -/
theorem pullback_e {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {ι : Type u} {family : ι → Over T.left}
    {x : (fppfQuotientStack G).p.Fiber T} {D : DescentDatum G family}
    (h : Corresponds G family x D) {ι' : Type u} {family' : ι' → Over T.left}
    (α : ι' → ι) (φ : ∀ j, family' j ⟶ family (α j)) (j : ι') :
    (h.pullback α φ).e j =
      atlasObjReindexIso G (DescentDatum.coverMap α φ j) (D.u (α j)) ≪≫
        (Chosen.reindex (fppfQuotientStack G).p (DescentDatum.coverMap α φ j)).mapIso (h.e (α j)) ≪≫
        (Chosen.Reindex.specifiedCompIsoApp (fppfQuotientStack G).p
            (coverHom family (α j)) (DescentDatum.coverMap α φ j)
            (DescentDatum.coverMap α φ j ≫ coverHom family (α j)) rfl x).symm ≪≫
        Chosen.Reindex.congrIsoApp (fppfQuotientStack G).p
          (DescentDatum.coverMap_coverHom α φ j) x := by
  dsimp only [pullback]
  rfl

end Corresponds

/-- Unfolding of `Corresponds` as chosen fibre isomorphisms realising the overlap arrows as
`π(r_ij)`. -/
theorem corresponds_iff {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {T : Over S} {ι : Type u} (family : ι → Over T.left)
    (x : (fppfQuotientStack G).p.Fiber T) (D : DescentDatum G family) :
    Nonempty (Corresponds G family x D) ↔
      ∃ e : ∀ i, atlasObj G (D.u i) ≅ Chosen.reindexObj (fppfQuotientStack G).p (coverHom family i) x,
        ∀ i j, IsPiArrow G family x D.u e (D.r i j) := by
  constructor
  · rintro ⟨h⟩
    exact ⟨h.e, h.overlap⟩
  · rintro ⟨e, h⟩
    exact ⟨⟨e, h⟩⟩

/-- A morphism of descent data agrees with a fibre morphism when each component is `π(r_i)`
after conjugating by the chosen correspondence isomorphisms. -/
def DescentDatum.Hom.agreesWith {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} {T : Over S} {ι : Type u} {family : ι → Over T.left}
    {D D' : DescentDatum G family} (ψ : DescentDatum.Hom D D')
    {x y : (fppfQuotientStack G).p.Fiber T}
    (hx : Corresponds G family x D) (hy : Corresponds G family y D') (φ : x ⟶ y) : Prop :=
  ∀ i,
    (sourceHomComparison G (D.u i) (ψ.r i) (ψ.source i)).hom ≫
        (hx.e i).hom ≫ Chosen.reindexMap (fppfQuotientStack G).p (coverHom family i) φ ≫ (hy.e i).inv ≫
        (targetHomComparison G (D'.u i) (ψ.r i) (ψ.target i)).inv =
      atlasArrow G (ψ.r i)

/-- `agreesWith` is conjugation of the restricted fibre morphism by the chosen correspondence
isomorphisms. -/
theorem DescentDatum.Hom.agreesWith_spec {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} {T : Over S} {ι : Type u} {family : ι → Over T.left}
    {D D' : DescentDatum G family} (ψ : DescentDatum.Hom D D')
    {x y : (fppfQuotientStack G).p.Fiber T}
    (hx : Corresponds G family x D) (hy : Corresponds G family y D') (φ : x ⟶ y) :
    ψ.agreesWith hx hy φ ↔
      ∀ i,
        (sourceHomComparison G (D.u i) (ψ.r i) (ψ.source i)).hom ≫
            (hx.e i).hom ≫ Chosen.reindexMap (fppfQuotientStack G).p (coverHom family i) φ ≫ (hy.e i).inv ≫
            (targetHomComparison G (D'.u i) (ψ.r i) (ψ.target i)).inv =
          atlasArrow G (ψ.r i) := by
  unfold DescentDatum.Hom.agreesWith
  with_reducible exact Iff.rfl

/-- Every fibre object of the fppf quotient stack is fppf-locally isomorphic to an atlas point. -/
theorem exists_fppfCovering_atlasIso {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {T : Over S} (x : (fppfQuotientStack G).p.Fiber T) :
    ∃ (ι : Type u) (family : ι → Over T.left)
      (u : ∀ i, ofOver (coverOver family i) ⟶ G.U.left),
      Scheme.FppfCovering family ∧
        ∀ i, Nonempty (atlasObj G (u i) ≅ Chosen.reindexObj (fppfQuotientStack G).p (coverHom family i) x) :=
  sorry

/-- The canonical overlap composites of local atlas presentations are induced by arrow-space points. -/
theorem exists_arrow_of_composedIso {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {T : Over S} {ι : Type u} (family : ι → Over T.left)
    (x : (fppfQuotientStack G).p.Fiber T)
    (u : ∀ i, ofOver (coverOver family i) ⟶ G.U.left)
    (e : ∀ i, atlasObj G (u i) ≅ Chosen.reindexObj (fppfQuotientStack G).p (coverHom family i) x) :
    ∃ r : ∀ i j, ofOver (pairOver family i j) ⟶ G.R.left,
      ∀ i j, IsPiArrow G family x u e (r i j) :=
  sorry

/-- Arrow-space points inducing the canonical overlap composites satisfy the descent equations. -/
theorem isDescentDatum_of_atlasIso {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {T : Over S} {ι : Type u} (family : ι → Over T.left)
    (x : (fppfQuotientStack G).p.Fiber T)
    (u : ∀ i, ofOver (coverOver family i) ⟶ G.U.left)
    (e : ∀ i, atlasObj G (u i) ≅ Chosen.reindexObj (fppfQuotientStack G).p (coverHom family i) x)
    (r : ∀ i j, ofOver (pairOver family i j) ⟶ G.R.left)
    (hπ : ∀ i j, IsPiArrow G family x u e (r i j)) :
    ∃ D : DescentDatum G family, D.u = u ∧ D.r = r :=
  sorry

/-- Every explicit descent datum on an fppf covering comes from a fibre object of the quotient stack. -/
theorem exists_fiberObj_of_descentDatum {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {T : Over S} {ι : Type u} (family : ι → Over T.left)
    (h_covering : Scheme.FppfCovering family) (D : DescentDatum G family) :
    ∃ x : (fppfQuotientStack G).p.Fiber T, Nonempty (Corresponds G family x D) :=
  sorry

/-- Fibre morphisms correspond uniquely in both directions to morphisms of their explicit descent data. -/
theorem fiberHom_existsUnique {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {T : Over S} {ι : Type u} (family : ι → Over T.left)
    (h_covering : Scheme.FppfCovering family)
    {x y : (fppfQuotientStack G).p.Fiber T} {D D' : DescentDatum G family}
    (hx : Corresponds G family x D) (hy : Corresponds G family y D') :
    (∀ φ : x ⟶ y, ∃! ψ : DescentDatum.Hom D D', ψ.agreesWith hx hy φ) ∧
      ∀ ψ : DescentDatum.Hom D D', ∃! φ : x ⟶ y, ψ.agreesWith hx hy φ :=
  sorry

/-- Agreement between fibre morphisms and descent morphisms is preserved and reflected by fppf refinement. -/
theorem corresponds_pullback {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {T : Over S} {ι : Type u} (family : ι → Over T.left)
    (h_covering : Scheme.FppfCovering family)
    {x : (fppfQuotientStack G).p.Fiber T} {D : DescentDatum G family}
    (hx : Corresponds G family x D) {ι' : Type u} (family' : ι' → Over T.left)
    (h_covering' : Scheme.FppfCovering family')
    (α : ι' → ι) (φ : ∀ j, family' j ⟶ family (α j)) :
    (∀ {y : (fppfQuotientStack G).p.Fiber T} {D' : DescentDatum G family}
        (hy : Corresponds G family y D') (φhom : x ⟶ y) (ψ : DescentDatum.Hom D D'),
        ψ.agreesWith hx hy φhom →
          (ψ.pullback α φ).agreesWith (hx.pullback α φ) (hy.pullback α φ) φhom) ∧
      ∀ {y : (fppfQuotientStack G).p.Fiber T} {D' : DescentDatum G family}
        (hy : Corresponds G family y D') (φhom : x ⟶ y) (ψ : DescentDatum.Hom D D'),
        (ψ.pullback α φ).agreesWith (hx.pullback α φ) (hy.pullback α φ) φhom →
          ψ.agreesWith hx hy φhom :=
  sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
