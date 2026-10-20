/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import ReasLib.CategoryTheory.GlueData
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.Tactic.CrossRefAttribute

/-!
# Doubling a scheme along an open subscheme

This file owns the explicit gluing construction, its two canonical charts,
the overlap, the descent interface, and the fold morphism.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

namespace DoubleAlong

variable {X : Scheme.{u}} (U : X.Opens)

namespace Impl

/-- The universe-lifted two-element index of the gluing presentation. -/
abbrev ChartIndex : Type u := ULift.{u} (Fin 2)

/-- The two copies of the ambient scheme in the gluing construction. -/
abbrev glueU (_ : ChartIndex) : Scheme.{u} := X

/-- The common open subscheme used as every off-diagonal overlap. -/
abbrev glueV (i j : ChartIndex) (_ : i ≠ j) : Scheme.{u} := U.toScheme

/-- The inclusion of an off-diagonal overlap into its source chart. -/
abbrev glueF (i j : ChartIndex) (hij : i ≠ j) : glueV U i j hij ⟶ X := U.ι

/-- The identity transition between the two presentations of the common overlap. -/
abbrev glueT (i j : ChartIndex) (hij : i ≠ j) :
    glueV U i j hij ⟶ glueV U j i hij.symm :=
  𝟙 _

/-- The identity comparison on intersections of off-diagonal overlaps. -/
noncomputable def glueT' (i j l : ChartIndex) (hij : i ≠ j) (hil : i ≠ l)
    (hjl : j ≠ l) :
    pullback (glueF U i j hij) (glueF U i l hil) ⟶
      pullback (glueF U j l hjl) (glueF U j i hij.symm) :=
  𝟙 _

/-- The intersection comparison is compatible with the transition maps. -/
theorem glueT'_fac (i j l : ChartIndex) (hij : i ≠ j) (hil : i ≠ l)
    (hjl : j ≠ l) :
    glueT' U i j l hij hil hjl ≫
        pullback.snd (glueF U j l hjl) (glueF U j i hij.symm) =
      pullback.fst (glueF U i j hij) (glueF U i l hil) ≫
        glueT U i j hij := sorry

/-- Opposite overlap transitions are inverse to one another. -/
theorem glueT_inv (i j : ChartIndex) (hij : i ≠ j) :
    glueT U i j hij ≫ glueT U j i hij.symm = 𝟙 _ := sorry

/-- The identity overlap transitions satisfy the gluing cocycle condition. -/
theorem glueT'_cocycle (i j l : ChartIndex) (hij : i ≠ j) (hil : i ≠ l)
    (hjl : j ≠ l) :
    glueT' U i j l hij hil hjl ≫
        glueT' U j l i hjl hij.symm hil.symm ≫
        glueT' U l i j hil.symm hjl.symm hij =
      𝟙 _ := sorry

/-- Off-diagonal gluing data for two copies of `X` identified along `U`. -/
noncomputable def glueData' : CategoryTheory.GlueData' Scheme.{u} where
  J := ChartIndex
  U := glueU (X := X)
  V := glueV U
  f := glueF U
  f_mono := inferInstance
  t := glueT U
  t' := glueT' U
  t_fac := glueT'_fac U
  t_inv := glueT_inv U
  cocycle := glueT'_cocycle U

/-- Every chart map in the completed gluing data is an open immersion. -/
theorem glueData_f_open (i j) :
    IsOpenImmersion
      ((CategoryTheory.GlueData.ofGlueData' (glueData' U)).f i j) := sorry

/-- Scheme gluing data for two copies of `X` identified along `U`. -/
noncomputable def glueData : Scheme.GlueData.{u} where
  toGlueData := CategoryTheory.GlueData.ofGlueData' (glueData' U)
  f_open := glueData_f_open U

end Impl

/-- The gluing datum for two copies of `X` identified along `U`. -/
@[stacks 01KL "doubled-scheme gluing datum"]
noncomputable abbrev glueData : Scheme.GlueData.{u} :=
  Impl.glueData U

end DoubleAlong

/-- The scheme obtained by gluing two copies of `X` along `U` by the identity. -/
@[stacks 01KL]
noncomputable def doubleAlong {X : Scheme.{u}} (U : X.Opens) : Scheme.{u} :=
  (DoubleAlong.glueData U).glued

namespace DoubleAlong

variable {X : Scheme.{u}} (U : X.Opens)

namespace Impl

/-- The implementation compatibility bridge used by the public descent map. -/
theorem compatible {Y : Scheme.{u}} (f : Fin 2 → (X ⟶ Y))
    (hf : U.ι ≫ f 0 = U.ι ≫ f 1) (i j : ChartIndex) :
    (glueData U).f i j ≫ f i.down =
      ((glueData U).t i j ≫ (glueData U).f j i) ≫ f j.down := sorry

/-- The implementation compatibility proof for the identity pair used by `fold`. -/
theorem foldAgreement : U.ι ≫ 𝟙 X = U.ι ≫ 𝟙 X := sorry

end Impl

/-- The canonical open immersion of the `i`-th copy of `X` into `doubleAlong U`. -/
@[stacks 01KL "doubled-scheme chart map"]
abbrev chartMap (i : Fin 2) : X ⟶ doubleAlong U :=
  (glueData U).ι (ULift.up i)

/-- A canonical chart map into the doubled scheme is an open immersion. -/
@[stacks 01KL "doubled-scheme chart open immersion", instance]
theorem chartMap_isOpenImmersion (i : Fin 2) :
    IsOpenImmersion (chartMap U i) := sorry

/-- The image of one of the two canonical charts in `doubleAlong U`. -/
@[stacks 01KL "doubled-scheme chart"]
abbrev chart (i : Fin 2) : (doubleAlong U).Opens :=
  (chartMap U i).opensRange

/-- The canonical identification of a doubled chart with the original scheme. -/
@[stacks 01KL "doubled-scheme chart isomorphism"]
noncomputable def chartIso (i : Fin 2) :
    (chart U i).toScheme ≅ X :=
  (chartMap U i).isoOpensRange.symm

/-- If `X` is affine, each canonical chart of `doubleAlong U` is affine. -/
@[stacks 01KL "doubled-scheme affine chart"]
theorem chart_isAffineOpen [IsAffine X] (i : Fin 2) :
    IsAffineOpen (chart U i) := sorry

/-- The two canonical charts cover `doubleAlong U`. -/
@[stacks 01KL "doubled-scheme chart cover"]
theorem chart_cover : chart U 0 ⊔ chart U 1 = ⊤ := sorry

/-- The common overlap mapped into `doubleAlong U` through the first chart. -/
@[stacks 01KL "doubled-scheme overlap map"]
noncomputable abbrev overlapMap : U.toScheme ⟶ doubleAlong U :=
  U.ι ≫ chartMap U 0

/-- The range of the common-overlap map is the intersection of the two canonical charts. -/
@[stacks 01KL "doubled-scheme overlap range"]
theorem overlapMap_opensRange :
    (overlapMap U).opensRange = chart U 0 ⊓ chart U 1 := sorry

/-- Mapping the common overlap through either chart gives the same morphism. -/
@[stacks 01KL "doubled-scheme overlap identification", reassoc]
theorem overlapMap_eq_secondChart :
    overlapMap U = U.ι ≫ chartMap U 1 := sorry

/-- If the doubled scheme is separated, the open along which it is glued is closed in `X`.

This is the generic geometric obstruction behind the standard doubled-origin examples. -/
@[stacks 01KL "separated doubling forces a closed overlap"]
theorem overlap_isClosed [(doubleAlong U).IsSeparated] :
    IsClosed (U : Set X) := sorry

/-- Doubling along an open which is not closed produces a non-separated scheme. -/
@[stacks 01KL "nonseparated doubling along a nonclosed open"]
theorem not_isSeparated_of_not_isClosed
    (hU : ¬ IsClosed (U : Set X)) :
    ¬ (doubleAlong U).IsSeparated := sorry

/-- If `X` is separated, doubling along an open `U` is separated whenever `U` is closed. -/
@[stacks 01KL "separated doubling along a closed open"]
theorem isSeparated_of_isClosed [X.IsSeparated]
    (hU : IsClosed (U : Set X)) :
    (doubleAlong U).IsSeparated := sorry

/-- For a separated scheme `X`, doubling along an open is separated exactly when the open is
closed in `X`. -/
@[stacks 01KL "separatedness criterion for doubled schemes"]
theorem isSeparated_iff [X.IsSeparated] :
    (doubleAlong U).IsSeparated ↔ IsClosed (U : Set X) := sorry

/-- Glue two morphisms `X ⟶ Y` that agree on `U` into a morphism `doubleAlong U ⟶ Y`. -/
@[stacks 01KL "doubled-scheme descent map"]
noncomputable def desc {Y : Scheme.{u}} (f : Fin 2 → (X ⟶ Y))
    (hf : U.ι ≫ f 0 = U.ι ≫ f 1) :
    doubleAlong U ⟶ Y :=
  (glueData U).toGlueData.desc Y (fun i ↦ f i.down) (Impl.compatible U f hf)

/-- The glued morphism restricts to the prescribed morphism on each canonical copy. -/
@[reassoc (attr := simp), stacks 01KL "doubled-scheme descent restriction"]
theorem chartMap_desc {Y : Scheme.{u}} (f : Fin 2 → (X ⟶ Y))
    (hf : U.ι ≫ f 0 = U.ι ≫ f 1) (i : Fin 2) :
    chartMap U i ≫ desc U f hf = f i := sorry

/-- Morphisms out of `doubleAlong U` are determined on the two canonical copies of `X`. -/
@[ext, stacks 01KL "doubled-scheme morphism extensionality"]
theorem hom_ext {Y : Scheme.{u}} {f g : doubleAlong U ⟶ Y}
    (h : ∀ i : Fin 2, chartMap U i ≫ f = chartMap U i ≫ g) :
    f = g := sorry

/-- A compatible pair glues to the unique morphism with the prescribed chart restrictions. -/
@[stacks 01KL "doubled-scheme descent uniqueness"]
theorem desc_unique {Y : Scheme.{u}} (f : Fin 2 → (X ⟶ Y))
    (hf : U.ι ≫ f 0 = U.ι ≫ f 1) (g : doubleAlong U ⟶ Y)
    (hg : ∀ i : Fin 2, chartMap U i ≫ g = f i) :
    g = desc U f hf := sorry

/-- A pair of morphisms from the two copies of `X` which agree after restriction to `U`. -/
@[stacks 01KL "compatible pair for doubled-scheme descent"]
def CompatiblePair (Y : Scheme.{u}) :=
  { f : Fin 2 → (X ⟶ Y) // U.ι ≫ f 0 = U.ι ≫ f 1 }

/-- Restricting a morphism from `doubleAlong U` to its two charts gives a compatible pair. -/
@[stacks 01KL "restriction to a compatible doubled-scheme pair"]
theorem restrictPair_compatible {Y : Scheme.{u}} (g : doubleAlong U ⟶ Y) :
    U.ι ≫ chartMap U 0 ≫ g = U.ι ≫ chartMap U 1 ≫ g := sorry

/-- Restrict a morphism from `doubleAlong U` to the two canonical copies of `X`. -/
@[stacks 01KL "doubled-scheme restriction pair"]
noncomputable def restrictPair {Y : Scheme.{u}} (g : doubleAlong U ⟶ Y) :
    CompatiblePair U Y :=
  ⟨fun i ↦ chartMap U i ≫ g, restrictPair_compatible U g⟩

/-- Descend a compatible pair of morphisms from the two canonical copies of `X`. -/
@[stacks 01KL "doubled-scheme compatible-pair descent"]
noncomputable def descPair {Y : Scheme.{u}} (f : CompatiblePair U Y) :
    doubleAlong U ⟶ Y :=
  desc U f.1 f.2

/-- Descending the restrictions of a morphism recovers that morphism. -/
@[stacks 01KL "doubled-scheme descent after restriction"]
theorem descPair_restrictPair {Y : Scheme.{u}} (g : doubleAlong U ⟶ Y) :
    descPair U (restrictPair U g) = g := sorry

/-- Restricting a descended compatible pair recovers the original pair. -/
@[stacks 01KL "doubled-scheme restriction after descent"]
theorem restrictPair_descPair {Y : Scheme.{u}} (f : CompatiblePair U Y) :
    restrictPair U (descPair U f) = f := sorry

/-- Morphisms from `doubleAlong U` are canonically equivalent to compatible pairs of morphisms
from `X`. -/
@[stacks 01KL "doubled scheme descent equivalence"]
noncomputable def homEquiv (Y : Scheme.{u}) :
    (doubleAlong U ⟶ Y) ≃ CompatiblePair U Y where
  toFun := restrictPair U
  invFun := descPair U
  left_inv := descPair_restrictPair U
  right_inv := restrictPair_descPair U

/-- The forward map of the doubled-scheme equivalence restricts a morphism to both charts. -/
@[simp, stacks 01KL "doubled-scheme descent equivalence forward map"]
theorem homEquiv_apply (Y : Scheme.{u}) (g : doubleAlong U ⟶ Y) :
    homEquiv U Y g = restrictPair U g := sorry

/-- The inverse map of the doubled-scheme equivalence descends a compatible pair. -/
@[simp, stacks 01KL "doubled-scheme descent equivalence inverse map"]
theorem homEquiv_symm_apply (Y : Scheme.{u}) (f : CompatiblePair U Y) :
    (homEquiv U Y).symm f = descPair U f := sorry

/-- The canonical fold morphism from `doubleAlong U` to `X`. -/
@[stacks 01KL "doubled-scheme fold"]
noncomputable def fold : doubleAlong U ⟶ X :=
  desc U (fun _ ↦ 𝟙 X) (Impl.foldAgreement U)

/-- The explicit comparison from a canonical chart to the original scheme, obtained by
restricting the fold. -/
@[stacks 01KL "doubled-scheme chart comparison"]
noncomputable abbrev chartComparison (i : Fin 2) : (chart U i).toScheme ⟶ X :=
  (chartIso U i).hom

/-- On each canonical chart, the fold is the explicit chart comparison. -/
@[reassoc (attr := simp), stacks 01KL "doubled-scheme chart comparison restriction"]
theorem chart_ι_fold (i : Fin 2) :
    (chart U i).ι ≫ fold U = chartComparison U i := sorry

/-- The restriction of a descended morphism to a canonical chart is its chart comparison followed
by the prescribed morphism from that copy of `X`. -/
@[reassoc (attr := simp), stacks 01KL "doubled-scheme chart descent restriction"]
theorem chart_ι_desc {Y : Scheme.{u}} (f : Fin 2 → (X ⟶ Y))
    (hf : U.ι ≫ f 0 = U.ι ≫ f 1) (i : Fin 2) :
    (chart U i).ι ≫ desc U f hf = chartComparison U i ≫ f i := sorry

/-- The fold restricts to the identity on each canonical copy of `X`. -/
@[reassoc (attr := simp), stacks 01KL "doubled-scheme fold restriction"]
theorem chartMap_fold (i : Fin 2) : chartMap U i ≫ fold U = 𝟙 X := sorry

/-- The fold is determined by its restrictions to the canonical charts. -/
@[stacks 01KL "doubled-scheme fold uniqueness"]
theorem fold_unique_chartMap (g : doubleAlong U ⟶ X)
    (hg : ∀ i : Fin 2, chartMap U i ≫ g = 𝟙 X) :
    g = fold U := sorry

/-- The copy of a point `x : X` lying in the `i`-th canonical chart. -/
@[stacks 01KL "point in a doubled-scheme chart"]
noncomputable def point (i : Fin 2) (x : X) : doubleAlong U :=
  (chartMap U i).base x

/-- The `i`-th copy of a point lies in the `i`-th canonical chart. -/
@[simp, stacks 01KL "doubled point belongs to its chart"]
theorem point_mem_chart (i : Fin 2) (x : X) :
    point U i x ∈ chart U i := sorry

/-- Folding either copy of a point recovers the original point. -/
@[simp, stacks 01KL "fold on doubled points"]
theorem fold_point (i : Fin 2) (x : X) :
    (fold U).base (point U i x) = x := sorry

/-- The fold identifies the images of the two canonical copies of every point. -/
@[stacks 01KL "fold identifies doubled points"]
theorem fold_point_zero_eq_one (x : X) :
    (fold U).base (point U 0 x) = (fold U).base (point U 1 x) := sorry

/-- A point in the gluing open has the same image in the two canonical charts. -/
@[stacks 01KL "doubled points agree on the gluing open"]
theorem point_zero_eq_point_one_of_mem (x : X) (hx : x ∈ U) :
    point U 0 x = point U 1 x := sorry

/-- A point outside the gluing open gives two distinct points in the doubled scheme. -/
@[stacks 01KL "doubled points differ off the gluing open"]
theorem point_zero_ne_point_one_of_not_mem (x : X) (hx : x ∉ U) :
    point U 0 x ≠ point U 1 x := sorry

/-- The two copies of a point are identified exactly on the gluing open. -/
@[simp, stacks 01KL "doubled-point identification criterion"]
theorem point_zero_eq_point_one_iff (x : X) :
    point U 0 x = point U 1 x ↔ x ∈ U := sorry

end DoubleAlong
end AlgebraicGeometry.Scheme
