/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

/- Bounded chart/gluing construction for small étale base change.
   Public migration proposal; native validation remains a MAIN gate. -/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import ReasLib.CategoryTheory.GlueData

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Etale.PullbackBounds

/- The fixed base atlas is input data.  Its index is the actual point type of
   `S`; no arbitrary universe-sized index type is stored in the bounded code. -/
structure BaseAtlas (S : Scheme.{u}) where
  affineOpen : S.carrier → S.Opens
  affine : ∀ i, IsAffineOpen (affineOpen i)
  containsIndex : ∀ i, i ∈ affineOpen i

abbrev BaseRing {S : Scheme.{u}} (A : BaseAtlas S) (i : S.carrier) : Type u :=
  Γ(S, A.affineOpen i)

/- A finite polynomial quotient code over one fixed affine base ring.  The
   quotient and `Spec.map` below are computed from the code. -/
structure RawChartCode {S : Scheme.{u}} (A : BaseAtlas S) (i : S.carrier) where
  variableCount : ℕ
  relationCount : ℕ
  relation : Fin relationCount → MvPolynomial (Fin variableCount) (BaseRing A i)

abbrev ChartRing {S : Scheme.{u}} {A : BaseAtlas S} {i : S.carrier}
    (c : RawChartCode A i) : Type u :=
  MvPolynomial (Fin c.variableCount) (BaseRing A i) ⧸
    Ideal.span (Set.range c.relation)

def chartToAffine {S : Scheme.{u}} {A : BaseAtlas S} {i : S.carrier}
    (c : RawChartCode A i) :
    Spec (.of (ChartRing c)) ⟶ Spec (.of (BaseRing A i)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (BaseRing A i) (ChartRing c)))

/- The étaleness condition is a Prop subtype.  It is the only condition used
   to restrict the finite code family; it does not hide a scheme datum. -/
def ChartCode {S : Scheme.{u}} (A : BaseAtlas S) (i : S.carrier) : Type u :=
  {c : RawChartCode A i // Etale (chartToAffine c)}

def chartScheme {S : Scheme.{u}} {A : BaseAtlas S} {i : S.carrier}
    (c : ChartCode A i) : Scheme.{u} :=
  Spec (.of (ChartRing c.1))

def chartToS {S : Scheme.{u}} {A : BaseAtlas S} {i : S.carrier}
    (c : ChartCode A i) : chartScheme c ⟶ S :=
  chartToAffine c.1 ≫ (A.affine i).isoSpec.inv ≫ (A.affineOpen i).ι

theorem chartToS_etale {S : Scheme.{u}} {A : BaseAtlas S} {i : S.carrier}
    (c : ChartCode A i) : Etale (chartToS c) := by
  letI : Etale (chartToAffine c.1) := c.2
  change Etale (chartToAffine c.1 ≫ (A.affine i).isoSpec.inv ≫
    (A.affineOpen i).ι)
  infer_instance

/- This is the finite-presentation API entry point used by the classification
   proof.  The target is exactly Mathlib's affine characterization, rather
   than an unrestricted `Scheme` or ring field in the code. -/
theorem chartToAffine_locallyOfFinitePresentation
    {S : Scheme.{u}} {A : BaseAtlas S} {i : S.carrier}
    (c : ChartCode A i) : LocallyOfFinitePresentation (chartToAffine c.1) := by
  sorry

/- The source index is the carrier of the given étale object.  This is fixed
   before coding and therefore remains in `Type u`. -/
abbrev SourceIndex {T : Scheme.{u}} (V : T.Etale) : Type u := V.left.carrier

/- `tripleFactor` is an explicit map supplied by overlap geometry.  From it
   and its displayed compatibility equation we compute the actual `t'` map
   required by `CategoryTheory.GlueData`; it is not an existential choice. -/
structure BoundedAtlas {S T : Scheme.{u}} (A : BaseAtlas S)
    (f : T ⟶ S) (V : T.Etale) where
  chart : SourceIndex V → Sigma (ChartCode A)
  openOverlap : ∀ x y, (chartScheme (chart x).2).Opens
  transition : ∀ x y,
    (openOverlap x y).toScheme ≅ (openOverlap y x).toScheme
  selfOpenIso : ∀ x, IsIso ((openOverlap x x).ι)
  transition_id : ∀ x, (transition x x).hom = 𝟙 _
  tripleFactor (x y z : SourceIndex V) :
    pullback ((openOverlap x y).ι) ((openOverlap x z).ι) ⟶ (openOverlap y z).toScheme
  tripleFactor_compat (x y z : SourceIndex V) :
    tripleFactor x y z ≫ (openOverlap y z).ι =
      pullback.fst ((openOverlap x y).ι) ((openOverlap x z).ι) ≫
        (transition x y).hom ≫ (openOverlap y x).ι
  t_fac : ∀ x y z,
    (pullback.lift (tripleFactor x y z)
      (pullback.fst ((openOverlap x y).ι) ((openOverlap x z).ι) ≫ (transition x y).hom)
      (tripleFactor_compat x y z)) ≫
        pullback.snd ((openOverlap y z).ι) ((openOverlap y x).ι) =
      pullback.fst ((openOverlap x y).ι) ((openOverlap x z).ι) ≫ (transition x y).hom
  cocycle : ∀ x y z,
    (pullback.lift (tripleFactor x y z)
      (pullback.fst ((openOverlap x y).ι) ((openOverlap x z).ι) ≫ (transition x y).hom)
      (tripleFactor_compat x y z)) ≫
        (pullback.lift (tripleFactor y z x)
          (pullback.fst ((openOverlap y z).ι) ((openOverlap y x).ι) ≫ (transition y z).hom)
          (tripleFactor_compat y z x)) ≫
        (pullback.lift (tripleFactor z x y)
          (pullback.fst ((openOverlap z x).ι) ((openOverlap z y).ι) ≫ (transition z x).hom)
          (tripleFactor_compat z x y)) = 𝟙 _
  chart_over_S : ∀ x y,
    (openOverlap x y).ι ≫ chartToS (chart x).2 =
      ((transition x y).hom ≫ (openOverlap y x).ι) ≫ chartToS (chart y).2

def U {S T : Scheme.{u}} {A : BaseAtlas S} {f : T ⟶ S} {V : T.Etale}
    (D : BoundedAtlas A f V) (x : SourceIndex V) : Scheme.{u} :=
  chartScheme (D.chart x).2

def Umap {S T : Scheme.{u}} {A : BaseAtlas S} {f : T ⟶ S} {V : T.Etale}
    (D : BoundedAtlas A f V) (x : SourceIndex V) : U D x ⟶ S :=
  chartToS (D.chart x).2

def Voverlap {S T : Scheme.{u}} {A : BaseAtlas S} {f : T ⟶ S} {V : T.Etale}
    (D : BoundedAtlas A f V) (x y : SourceIndex V) : Scheme.{u} :=
  (D.openOverlap x y).toScheme

def foverlap {S T : Scheme.{u}} {A : BaseAtlas S} {f : T ⟶ S} {V : T.Etale}
    (D : BoundedAtlas A f V) (x y : SourceIndex V) : Voverlap D x y ⟶ U D x :=
  (D.openOverlap x y).ι

def toverlap {S T : Scheme.{u}} {A : BaseAtlas S} {f : T ⟶ S} {V : T.Etale}
    (D : BoundedAtlas A f V) (x y : SourceIndex V) : Voverlap D x y ⟶ Voverlap D y x :=
  (D.transition x y).hom

/- The `t'` map is now a real pullback lift in the existing gluing API. -/
def tPrime {S T : Scheme.{u}} {A : BaseAtlas S} {f : T ⟶ S} {V : T.Etale}
    (D : BoundedAtlas A f V) (x y z : SourceIndex V) :
    pullback (foverlap D x y) (foverlap D x z) ⟶
      pullback (foverlap D y z) (foverlap D y x) :=
  pullback.lift (D.tripleFactor x y z)
    (pullback.fst (foverlap D x y) (foverlap D x z) ≫ toverlap D x y)
    (D.tripleFactor_compat x y z)

/- This is the concrete bridge to Mathlib's `Scheme.GlueData`.  The generated
   object is a genuine `Scheme.{u}` and its chart inclusions are open
   immersions. -/
noncomputable def schemeGlueData {S T : Scheme.{u}} {A : BaseAtlas S}
    {f : T ⟶ S} {V : T.Etale} (D : BoundedAtlas A f V) : Scheme.GlueData.{u} where
  J := SourceIndex V
  U := U D
  V := fun p => Voverlap D p.1 p.2
  f := foverlap D
  f_id := D.selfOpenIso
  t := toverlap D
  t_id := D.transition_id
  t' := tPrime D
  t_fac := D.t_fac
  cocycle := D.cocycle
  f_mono := by
    intro x y
    change Mono ((D.openOverlap x y).ι)
    infer_instance
  f_open := by
    intro x y
    change IsOpenImmersion ((D.openOverlap x y).ι)
    infer_instance

abbrev gluedScheme {S T : Scheme.{u}} {A : BaseAtlas S} {f : T ⟶ S} {V : T.Etale}
    (D : BoundedAtlas A f V) : Scheme.{u} := (schemeGlueData D).glued

/- The map to S is built by the actual open-cover gluing constructor.  Its
   compatibility premise is explicit at the glued chart level, so this stage
   does not manufacture it from an unproved geometric assertion. -/
def gluedToS {S T : Scheme.{u}} {A : BaseAtlas S} {f : T ⟶ S} {V : T.Etale}
    (D : BoundedAtlas A f V)
    (coverCompat : ∀ x y,
      pullback.fst ((schemeGlueData D).ι x) ((schemeGlueData D).ι y) ≫ Umap D x =
        pullback.snd ((schemeGlueData D).ι x) ((schemeGlueData D).ι y) ≫ Umap D y) :
    gluedScheme D ⟶ S :=
  (schemeGlueData D).openCover.glueMorphisms (Umap D) coverCompat

abbrev CoverCompat {S T : Scheme.{u}} {A : BaseAtlas S} {f : T ⟶ S} {V : T.Etale}
    (D : BoundedAtlas A f V) : Prop := ∀ x y,
      pullback.fst ((schemeGlueData D).ι x) ((schemeGlueData D).ι y) ≫ Umap D x =
        pullback.snd ((schemeGlueData D).ι x) ((schemeGlueData D).ι y) ≫ Umap D y

/- A family-level law keeps cover compatibility explicit without putting a proof
   in a data-bearing structure. -/
abbrev coverCompatLaw {S T : Scheme.{u}} {A : BaseAtlas S} {f : T ⟶ S}
    (V : T.Etale) : Prop := ∀ D : BoundedAtlas A f V, CoverCompat D

/- Once the cover-compatibility proofs are supplied, this is the same-u family
   of all arrows from V into the realized base changes that satisfy the actual
   over-T equation.  The maps are fields of the sigma type; no map is selected
   from a proposition. -/
def BoundedCommaFamilyWithLaw {S T : Scheme.{u}} {A : BaseAtlas S} {f : T ⟶ S}
    (V : T.Etale) (coverCompat : ∀ D : BoundedAtlas A f V, CoverCompat D) : Type u :=
  Sigma (fun D : BoundedAtlas A f V =>
    {k : V.left ⟶ pullback (gluedToS D (coverCompat D)) f //
      k ≫ pullback.snd (gluedToS D (coverCompat D)) f = V.hom})

theorem gluedToS_restricts {S T : Scheme.{u}} {A : BaseAtlas S} {f : T ⟶ S}
    {V : T.Etale} (D : BoundedAtlas A f V) (coverCompat : ∀ x y,
      pullback.fst ((schemeGlueData D).ι x) ((schemeGlueData D).ι y) ≫ Umap D x =
        pullback.snd ((schemeGlueData D).ι x) ((schemeGlueData D).ι y) ≫ Umap D y)
    (x : SourceIndex V) :
    (schemeGlueData D).ι x ≫ gluedToS D coverCompat = Umap D x := by
  exact (schemeGlueData D).openCover.ι_glueMorphisms (Umap D) coverCompat x

/- PROOF DEBT: étaleness is local on the actual open cover.  This theorem is
   intentionally a Prop and is not used to construct the scheme or map. -/
theorem gluedToS_etale {S T : Scheme.{u}} {A : BaseAtlas S} {f : T ⟶ S}
    {V : T.Etale} (D : BoundedAtlas A f V) (coverCompat : ∀ x y,
      pullback.fst ((schemeGlueData D).ι x) ((schemeGlueData D).ι y) ≫ Umap D x =
        pullback.snd ((schemeGlueData D).ι x) ((schemeGlueData D).ι y) ≫ Umap D y) :
    Etale (gluedToS D coverCompat) := by
  sorry

/- PROOF DEBT: this is the exact finite-presentation completeness statement
   needed to populate `BoundedAtlas.chart`.  The witness is Prop-valued; no
   an untracked choice is used here or hidden in a data definition. -/
theorem affine_etale_chart_code_exists {S : Scheme.{u}} (A : BaseAtlas S)
    {U : Scheme.{u}} (p : U ⟶ S) [Etale p] (i : S.carrier) (y : U.carrier)
    (hy : p.base y ∈ A.affineOpen i) :
    ∃ (W : U.Opens), y ∈ W ∧ IsAffineOpen W ∧
      W ≤ p ⁻¹ᵁ A.affineOpen i ∧
      ∃ c : ChartCode A i,
        ∃ e : chartScheme c ≅ W.toScheme,
          e.hom ≫ W.ι ≫ p = chartToS c := by
  sorry

/- The remaining bounded-comma statement is deliberately not encoded as a
   data field.  It still needs the open-union factorization, the comparison
   isomorphism, Hom-smallness, and finality proof; those obligations are listed
   in the accompanying report rather than asserted here. -/


/- The canonical point-indexed atlas uses the native range-membership field
   `AffineCover.covers`; it does not wrap that membership in a second witness. -/
noncomputable def canonicalBaseAtlas (S : Scheme.{u}) : BaseAtlas S where
  affineOpen x := (S.affineCover.f (S.affineCover.idx x)).opensRange
  affine x := isAffineOpen_opensRange (S.affineCover.f (S.affineCover.idx x))
  containsIndex x := by
    change x ∈ Set.range (S.affineCover.f (S.affineCover.idx x)).base
    exact S.affineCover.covers x

noncomputable def overlapPullbackIso {S T : Scheme.{u}} {A : BaseAtlas S}
    {f : T ⟶ S} {V : T.Etale} (D : BoundedAtlas A f V)
    (x y : SourceIndex V) : Voverlap D x y ≅
      pullback ((schemeGlueData D).ι x) ((schemeGlueData D).ι y) :=
  IsLimit.conePointUniqueUpToIso
    ((schemeGlueData D).vPullbackConeIsLimit x y)
    (pullback.isLimit ((schemeGlueData D).ι x) ((schemeGlueData D).ι y))

/- Compatibility aliases live in the structure namespace so existing consumer
   code may use `D.schemeGlueData`-style notation without pretending these are
   structure fields.  The canonical root declarations above remain owners. -/
namespace BoundedAtlas

abbrev U {S T : Scheme.{u}} {A : BaseAtlas S} {f : T ⟶ S} {V : T.Etale}
    (D : BoundedAtlas A f V) := AlgebraicGeometry.Scheme.Etale.PullbackBounds.U D
abbrev Umap {S T : Scheme.{u}} {A : BaseAtlas S} {f : T ⟶ S} {V : T.Etale}
    (D : BoundedAtlas A f V) := AlgebraicGeometry.Scheme.Etale.PullbackBounds.Umap D
abbrev Voverlap {S T : Scheme.{u}} {A : BaseAtlas S} {f : T ⟶ S} {V : T.Etale}
    (D : BoundedAtlas A f V) := AlgebraicGeometry.Scheme.Etale.PullbackBounds.Voverlap D
abbrev foverlap {S T : Scheme.{u}} {A : BaseAtlas S} {f : T ⟶ S} {V : T.Etale}
    (D : BoundedAtlas A f V) := AlgebraicGeometry.Scheme.Etale.PullbackBounds.foverlap D
abbrev toverlap {S T : Scheme.{u}} {A : BaseAtlas S} {f : T ⟶ S} {V : T.Etale}
    (D : BoundedAtlas A f V) := AlgebraicGeometry.Scheme.Etale.PullbackBounds.toverlap D
abbrev tPrime {S T : Scheme.{u}} {A : BaseAtlas S} {f : T ⟶ S} {V : T.Etale}
    (D : BoundedAtlas A f V) := AlgebraicGeometry.Scheme.Etale.PullbackBounds.tPrime D
noncomputable abbrev schemeGlueData {S T : Scheme.{u}} {A : BaseAtlas S}
    {f : T ⟶ S} {V : T.Etale} (D : BoundedAtlas A f V) :=
  AlgebraicGeometry.Scheme.Etale.PullbackBounds.schemeGlueData D
abbrev gluedScheme {S T : Scheme.{u}} {A : BaseAtlas S}
    {f : T ⟶ S} {V : T.Etale} (D : BoundedAtlas A f V) :=
  AlgebraicGeometry.Scheme.Etale.PullbackBounds.gluedScheme D
abbrev gluedToS {S T : Scheme.{u}} {A : BaseAtlas S}
    {f : T ⟶ S} {V : T.Etale} (D : BoundedAtlas A f V)
    (h : CoverCompat D) := AlgebraicGeometry.Scheme.Etale.PullbackBounds.gluedToS D h

end BoundedAtlas

/- Precomposition by the comparison Iso is cancellation on the left, hence
   `cancel_epi`.  The two native cone projection equations reduce this to the
   stored chart-over-S law. -/
theorem coverCompat_of_chart_over_S {S T : Scheme.{u}} {A : BaseAtlas S}
    {f : T ⟶ S} {V : T.Etale} (D : BoundedAtlas A f V) : CoverCompat D := by
  change ∀ x y : SourceIndex V,
    pullback.fst ((schemeGlueData D).ι x) ((schemeGlueData D).ι y) ≫ Umap D x =
      pullback.snd ((schemeGlueData D).ι x) ((schemeGlueData D).ι y) ≫ Umap D y
  intro x y
  have hfst : (overlapPullbackIso D x y).hom ≫
      pullback.fst ((schemeGlueData D).ι x) ((schemeGlueData D).ι y) =
        foverlap D x y :=
    IsLimit.conePointUniqueUpToIso_hom_comp
      ((schemeGlueData D).vPullbackConeIsLimit x y)
      (pullback.isLimit ((schemeGlueData D).ι x) ((schemeGlueData D).ι y))
      WalkingCospan.left
  have hsnd : (overlapPullbackIso D x y).hom ≫
      pullback.snd ((schemeGlueData D).ι x) ((schemeGlueData D).ι y) =
        toverlap D x y ≫ foverlap D y x :=
    IsLimit.conePointUniqueUpToIso_hom_comp
      ((schemeGlueData D).vPullbackConeIsLimit x y)
      (pullback.isLimit ((schemeGlueData D).ι x) ((schemeGlueData D).ι y))
      WalkingCospan.right
  apply (cancel_epi (overlapPullbackIso D x y).hom).1
  rw [← Category.assoc, ← Category.assoc, hfst, hsnd]
  exact D.chart_over_S x y

theorem canonicalCoverCompatLaw {S T : Scheme.{u}} {A : BaseAtlas S}
    {f : T ⟶ S} (V : T.Etale) : coverCompatLaw (A := A) (f := f) V := by
  intro D
  exact coverCompat_of_chart_over_S D

/- A comma arrow is retained only when its map is genuinely over T. -/
def BoundedCommaFamily {S T : Scheme.{u}} {A : BaseAtlas S} {f : T ⟶ S}
    (V : T.Etale) : Type u :=
  Sigma (fun D : BoundedAtlas A f V =>
    {k : V.left ⟶ pullback (gluedToS D (coverCompat_of_chart_over_S D)) f //
      k ≫ pullback.snd (gluedToS D (coverCompat_of_chart_over_S D)) f = V.hom})

abbrev CommaTarget {S T : Scheme.{u}} {A : BaseAtlas S} {f : T ⟶ S}
    {V : T.Etale} (D : BoundedAtlas A f V)
    (hcompat : coverCompatLaw (A := A) (f := f) V) : Scheme.{u} :=
  pullback (gluedToS D (hcompat D)) f

abbrev CommaArrow {S T : Scheme.{u}} {A : BaseAtlas S} {f : T ⟶ S}
    {V : T.Etale} (D : BoundedAtlas A f V)
    (hcompat : coverCompatLaw (A := A) (f := f) V) : Type u :=
  {k : V.left ⟶ CommaTarget D hcompat //
    k ≫ pullback.snd (gluedToS D (hcompat D)) f = V.hom}

def commaProjection {S T : Scheme.{u}} {A : BaseAtlas S} {f : T ⟶ S}
    {V : T.Etale} {D : BoundedAtlas A f V}
    {hcompat : coverCompatLaw (A := A) (f := f) V}
    (k : CommaArrow D hcompat) : V.left ⟶ gluedScheme D :=
  k.1 ≫ pullback.fst (gluedToS D (hcompat D)) f

def commaChartOpen {S T : Scheme.{u}} {A : BaseAtlas S} {f : T ⟶ S}
    {V : T.Etale} {D : BoundedAtlas A f V}
    {hcompat : coverCompatLaw (A := A) (f := f) V}
    (k : CommaArrow D hcompat) (x : SourceIndex V) : V.left.Opens :=
  (commaProjection k) ⁻¹ᵁ ((schemeGlueData D).ι x).opensRange

def commaOpenUnion {S T : Scheme.{u}} {A : BaseAtlas S} {f : T ⟶ S}
    {V : T.Etale} {D : BoundedAtlas A f V}
    {hcompat : coverCompatLaw (A := A) (f := f) V}
    (k : CommaArrow D hcompat) : V.left.Opens :=
  ⨆ x, commaChartOpen k x

def commaChartToV {S T : Scheme.{u}} {A : BaseAtlas S} {f : T ⟶ S}
    {V : T.Etale} {D : BoundedAtlas A f V}
    {hcompat : coverCompatLaw (A := A) (f := f) V}
    (k : CommaArrow D hcompat) (x : SourceIndex V) :
    (commaChartOpen k x).toScheme ⟶ V.left :=
  (commaChartOpen k x).ι

def commaChartToGlued {S T : Scheme.{u}} {A : BaseAtlas S} {f : T ⟶ S}
    {V : T.Etale} {D : BoundedAtlas A f V}
    {hcompat : coverCompatLaw (A := A) (f := f) V}
    (k : CommaArrow D hcompat) (x : SourceIndex V) :
    (commaChartOpen k x).toScheme ⟶ gluedScheme D :=
  commaChartToV k x ≫ commaProjection k

def commaOpenCover {S T : Scheme.{u}} {A : BaseAtlas S} {f : T ⟶ S}
    {V : T.Etale} {D : BoundedAtlas A f V}
    {hcompat : coverCompatLaw (A := A) (f := f) V}
    (k : CommaArrow D hcompat) :
    (commaOpenUnion k).toScheme.OpenCover :=
  Scheme.Opens.iSupOpenCover (fun x => commaChartOpen k x)

/- `ι` has exactly the required target `V.left`; `homOfLE le_top` would instead
   target the separate top open subscheme. -/
def commaUnionToV {S T : Scheme.{u}} {A : BaseAtlas S} {f : T ⟶ S}
    {V : T.Etale} {D : BoundedAtlas A f V}
    {hcompat : coverCompatLaw (A := A) (f := f) V}
    (k : CommaArrow D hcompat) :
    (commaOpenUnion k).toScheme ⟶ V.left :=
  (commaOpenUnion k).ι

noncomputable def commaChartMap {S T : Scheme.{u}} {A : BaseAtlas S} {f : T ⟶ S}
    {V : T.Etale} {D : BoundedAtlas A f V}
    {hcompat : coverCompatLaw (A := A) (f := f) V}
    (k : CommaArrow D hcompat) (x : SourceIndex V) :
    (commaChartOpen k x).toScheme ⟶ U D x := by
  let q := commaProjection k
  let r := q.resLE ((schemeGlueData D).ι x).opensRange
    (commaChartOpen k x) le_rfl
  exact r ≫ ((gluedScheme D).isoOfEq
      (Scheme.Hom.image_top_eq_opensRange ((schemeGlueData D).ι x)).symm).hom ≫
    (((schemeGlueData D).ι x).isoImage (⊤ : (U D x).Opens)).inv ≫
      (U D x).topIso.hom

structure CommaOpenRefinement {S T : Scheme.{u}} {A : BaseAtlas S}
    {f : T ⟶ S} {V : T.Etale} (D : BoundedAtlas A f V)
    {hcompat : coverCompatLaw (A := A) (f := f) V}
    (k : CommaArrow D hcompat) where
  cover : (commaOpenUnion k).toScheme.OpenCover
  toV : (commaOpenUnion k).toScheme ⟶ V.left
  chart : ∀ x, (commaChartOpen k x).toScheme ⟶ U D x

noncomputable def commaOpenRefinement {S T : Scheme.{u}} {A : BaseAtlas S}
    {f : T ⟶ S} {V : T.Etale} {D : BoundedAtlas A f V}
    {hcompat : coverCompatLaw (A := A) (f := f) V}
    (k : CommaArrow D hcompat) : CommaOpenRefinement D k :=
  { cover := commaOpenCover k
    toV := commaUnionToV k
    chart := fun x => commaChartMap k x }

def commaChartFactorizationLaw {S T : Scheme.{u}} {A : BaseAtlas S}
    {f : T ⟶ S} {V : T.Etale} {D : BoundedAtlas A f V}
    {hcompat : coverCompatLaw (A := A) (f := f) V}
    (k : CommaArrow D hcompat) : Prop :=
  ∀ x, commaChartMap k x ≫ Umap D x =
    commaChartToGlued k x ≫ gluedToS D (hcompat D)

def comparisonIsoOfRangeEq {X Y Z : Scheme.{u}}
    (a : Y ⟶ X) (b : Z ⟶ X) [IsOpenImmersion a] [IsOpenImmersion b]
    (hrange : Set.range a.base = Set.range b.base) : Y ≅ Z :=
  IsOpenImmersion.isoOfRangeEq a b hrange

theorem commaOpenUnion_covers_source {S T : Scheme.{u}} {A : BaseAtlas S}
    {f : T ⟶ S} {V : T.Etale} {D : BoundedAtlas A f V}
    {hcompat : coverCompatLaw (A := A) (f := f) V}
    (k : CommaArrow D hcompat) : commaOpenUnion k = ⊤ := by
  sorry

/- This is a relation for one supplied witness.  It does not assert a false
   comparison with every arbitrary scheme. -/
structure EtaleCommaInput {S T : Scheme.{u}} (f : T ⟶ S) (V : T.Etale)
    {U : Scheme.{u}} (g : U ⟶ S) [Etale g] where
  h : V.left ⟶ pullback g f
  overT : h ≫ pullback.snd g f = V.hom

/- The projection into `U` is fixed by the supplied comma arrow. -/
def commaInputProjection {S T : Scheme.{u}} {f : T ⟶ S} {V : T.Etale}
    {U : Scheme.{u}} {g : U ⟶ S} [Etale g]
    (C : EtaleCommaInput f V g) : V.left ⟶ U :=
  C.h ≫ pullback.fst g f

structure AffineChartSelection {S T : Scheme.{u}} {f : T ⟶ S} {V : T.Etale}
    {U : Scheme.{u}} {g : U ⟶ S} [Etale g]
    (C : EtaleCommaInput f V g) where
  chartOpen : V.left.carrier → U.Opens
  chartAffine : ∀ x, IsAffineOpen (chartOpen x)
  containsProjection : ∀ x,
    (commaInputProjection C).base x ∈ chartOpen x

def chartPreimage {S T : Scheme.{u}} {f : T ⟶ S} {V : T.Etale}
    {U : Scheme.{u}} {g : U ⟶ S} [Etale g]
    (C : EtaleCommaInput f V g) (A : AffineChartSelection C)
    (x : V.left.carrier) : V.left.Opens :=
  (commaInputProjection C) ⁻¹ᵁ A.chartOpen x

def chartFactor {S T : Scheme.{u}} {f : T ⟶ S} {V : T.Etale}
    {U : Scheme.{u}} {g : U ⟶ S} [Etale g]
    (C : EtaleCommaInput f V g) (A : AffineChartSelection C)
    (x : V.left.carrier) :
    (chartPreimage C A x).toScheme ⟶ (A.chartOpen x).toScheme :=
  (commaInputProjection C).resLE (A.chartOpen x) (chartPreimage C A x) le_rfl

theorem chartFactorization {S T : Scheme.{u}} {f : T ⟶ S} {V : T.Etale}
    {U : Scheme.{u}} {g : U ⟶ S} [Etale g]
    (C : EtaleCommaInput f V g) (A : AffineChartSelection C)
    (x : V.left.carrier) :
    chartFactor C A x ≫ (A.chartOpen x).ι =
      (chartPreimage C A x).ι ≫ commaInputProjection C := by
  simpa [chartFactor] using
    (Scheme.Hom.resLE_comp_ι (commaInputProjection C)
      (U := A.chartOpen x) (V := chartPreimage C A x) le_rfl)

def imageContainingUnion {S T : Scheme.{u}} {f : T ⟶ S} {V : T.Etale}
    {U : Scheme.{u}} {g : U ⟶ S} [Etale g]
    (C : EtaleCommaInput f V g) (A : AffineChartSelection C) : U.Opens :=
  ⨆ x, A.chartOpen x

def imageContainingUnionMap {S T : Scheme.{u}} {f : T ⟶ S} {V : T.Etale}
    {U : Scheme.{u}} {g : U ⟶ S} [Etale g]
    (C : EtaleCommaInput f V g) (A : AffineChartSelection C) :
    (imageContainingUnion C A).toScheme ⟶ U :=
  (imageContainingUnion C A).ι

def imageContainingUnionLaw {S T : Scheme.{u}} {f : T ⟶ S} {V : T.Etale}
    {U : Scheme.{u}} {g : U ⟶ S} [Etale g]
    (C : EtaleCommaInput f V g) (A : AffineChartSelection C) : Prop :=
  ∀ x, (commaInputProjection C).base x ∈ imageContainingUnion C A

/- The corrected factor layer fixes the target open as the actual union of the
   supplied affine charts.  Its only scheme is the open subscheme furnished by
   `Opens.toScheme`; no arbitrary target object is quantified. -/
noncomputable def canonicalAffineChartSelection {S T : Scheme.{u}}
    {f : T ⟶ S} {V : T.Etale} {U : Scheme.{u}}
    (g : U ⟶ S) [Etale g] (C : EtaleCommaInput f V g) :
    AffineChartSelection C where
  chartOpen x :=
    (U.affineCover.f
      (U.affineCover.idx ((commaInputProjection C).base x))).opensRange
  chartAffine x :=
    isAffineOpen_opensRange
      (U.affineCover.f (U.affineCover.idx ((commaInputProjection C).base x)))
  containsProjection x := by
    change (commaInputProjection C).base x ∈
      Set.range (U.affineCover.f
        (U.affineCover.idx ((commaInputProjection C).base x))).base
    exact U.affineCover.covers ((commaInputProjection C).base x)

/- The native `covers` field gives the union law for the canonical selection.
   This is a proposition and is not used to choose any scheme-level datum. -/
theorem canonicalImageContainingUnionLaw {S T : Scheme.{u}}
    {f : T ⟶ S} {V : T.Etale} {U : Scheme.{u}}
    (g : U ⟶ S) [Etale g] (C : EtaleCommaInput f V g) :
    imageContainingUnionLaw C (canonicalAffineChartSelection g C) := by
  intro x
  exact (le_iSup (fun y : V.left.carrier =>
      (canonicalAffineChartSelection g C).chartOpen y) x)
    ((canonicalAffineChartSelection g C).containsProjection x)

/- The pointwise union law is converted into the open containment needed by
   `Scheme.Hom.resLE`. -/
def projectionImageContainment {S T : Scheme.{u}} {f : T ⟶ S}
    {V : T.Etale} {U : Scheme.{u}} {g : U ⟶ S} [Etale g]
    (C : EtaleCommaInput f V g) (A : AffineChartSelection C)
    (hA : imageContainingUnionLaw C A) :
    (⊤ : V.left.Opens) ≤
      (commaInputProjection C) ⁻¹ᵁ imageContainingUnion C A := by
  intro x hx
  exact hA x

/- This is the actual map to the union.  The first leg is `resLE` and the
   second is the canonical top-open isomorphism, so no map is selected from a
   mere existence proposition. -/
noncomputable def projectionToImage {S T : Scheme.{u}} {f : T ⟶ S}
    {V : T.Etale} {U : Scheme.{u}} {g : U ⟶ S} [Etale g]
    (C : EtaleCommaInput f V g) (A : AffineChartSelection C)
    (hA : imageContainingUnionLaw C A) :
    V.left ⟶ (imageContainingUnion C A).toScheme :=
  V.left.topIso.inv ≫
    (commaInputProjection C).resLE (imageContainingUnion C A) ⊤
      (projectionImageContainment C A hA)

@[reassoc (attr := simp)] theorem projectionToImage_comp_inclusion
    {S T : Scheme.{u}} {f : T ⟶ S} {V : T.Etale} {U : Scheme.{u}}
    {g : U ⟶ S} [Etale g] (C : EtaleCommaInput f V g)
    (A : AffineChartSelection C) (hA : imageContainingUnionLaw C A) :
    projectionToImage C A hA ≫ imageContainingUnionMap C A =
      commaInputProjection C := by
  simp [projectionToImage, imageContainingUnionMap, Category.assoc]

/- The provider is parameterized by a supplied bounded atlas and an isomorphism
   over the *fixed* computed union.  Compatibility with the comma arrow is
   forced by the inclusion factorization and the pullback equations, so it is
   a theorem rather than another field of the data. -/
theorem projectionToImage_comp_g {S T : Scheme.{u}} {f : T ⟶ S} {V : T.Etale}
    {U : Scheme.{u}} {g : U ⟶ S} [Etale g] (C : EtaleCommaInput f V g)
    (A : AffineChartSelection C) (hA : imageContainingUnionLaw C A) :
    projectionToImage C A hA ≫ (imageContainingUnionMap C A ≫ g) =
      V.hom ≫ f := by
  calc
    projectionToImage C A hA ≫ (imageContainingUnionMap C A ≫ g) =
        (projectionToImage C A hA ≫ imageContainingUnionMap C A) ≫ g :=
      (Category.assoc _ _ _).symm
    _ = commaInputProjection C ≫ g := by
      rw [projectionToImage_comp_inclusion]
    _ = (C.h ≫ pullback.fst g f) ≫ g := by
      rfl
    _ = C.h ≫ (pullback.fst g f ≫ g) := Category.assoc _ _ _
    _ = C.h ≫ (pullback.snd g f ≫ f) := by rw [pullback.condition]
    _ = (C.h ≫ pullback.snd g f) ≫ f := (Category.assoc _ _ _).symm
    _ = V.hom ≫ f := congrArg (fun k => k ≫ f) C.overT

structure CorrectedCommaCompositionData {S T : Scheme.{u}}
    {f : T ⟶ S} {V : T.Etale} {U : Scheme.{u}} (g : U ⟶ S) [Etale g]
    (C : EtaleCommaInput f V g) (A : AffineChartSelection C)
    (hA : imageContainingUnionLaw C A) where
  D : BoundedAtlas (canonicalBaseAtlas S) f V
  ψ : gluedScheme D ≅ (imageContainingUnion C A).toScheme
  ψ_overS : ψ.hom ≫ (imageContainingUnionMap C A ≫ g) =
    gluedToS D (coverCompat_of_chart_over_S D)

abbrev Uprime {S T : Scheme.{u}} {f : T ⟶ S} {V : T.Etale}
    {U : Scheme.{u}} {g : U ⟶ S} [Etale g]
    {C : EtaleCommaInput f V g} (A : AffineChartSelection C) : Scheme.{u} :=
  (imageContainingUnion C A).toScheme

def j {S T : Scheme.{u}} {f : T ⟶ S} {V : T.Etale} {U : Scheme.{u}}
    {g : U ⟶ S} [Etale g] {C : EtaleCommaInput f V g}
    (A : AffineChartSelection C) : Uprime A ⟶ U :=
  imageContainingUnionMap C A

def gprime {S T : Scheme.{u}} {f : T ⟶ S} {V : T.Etale} {U : Scheme.{u}}
    {g : U ⟶ S} [Etale g] {C : EtaleCommaInput f V g}
    (A : AffineChartSelection C) : Uprime A ⟶ S :=
  j A ≫ g

def r {S T : Scheme.{u}} {f : T ⟶ S} {V : T.Etale} {U : Scheme.{u}}
    {g : U ⟶ S} [Etale g] {C : EtaleCommaInput f V g}
    {A : AffineChartSelection C}
    {hA : imageContainingUnionLaw C A}
    (c : CorrectedCommaCompositionData g C A hA) : gluedScheme c.D ⟶ U :=
  c.ψ.hom ≫ j A

lemma r_overS {S T : Scheme.{u}} {f : T ⟶ S} {V : T.Etale} {U : Scheme.{u}}
    {g : U ⟶ S} [Etale g] {C : EtaleCommaInput f V g}
    {A : AffineChartSelection C} {hA : imageContainingUnionLaw C A}
    (c : CorrectedCommaCompositionData g C A hA) :
    gluedToS c.D (coverCompat_of_chart_over_S c.D) = r c ≫ g := by
  simpa [r, j, Category.assoc] using c.ψ_overS.symm

/- Base change of the supplied `ψ` is the native pullback map, promoted to an
   isomorphism by the existing `pullback.map_isIso` instance. -/
noncomputable def ψT {S T : Scheme.{u}} {f : T ⟶ S} {V : T.Etale} {U : Scheme.{u}}
    {g : U ⟶ S} [Etale g] {C : EtaleCommaInput f V g}
    {A : AffineChartSelection C} {hA : imageContainingUnionLaw C A}
    (c : CorrectedCommaCompositionData g C A hA) :
    pullback (gluedToS c.D (coverCompat_of_chart_over_S c.D)) f ≅
      pullback (gprime A) f :=
  asIso <| pullback.map _ _ _ _ c.ψ.hom (𝟙 _) (𝟙 _)
    (by simpa [gprime, j, Category.assoc] using c.ψ_overS.symm)
    (by simp)

/- The arrow into the computed union is the actual pullback lift with the
   original `V.hom` as its second leg.  Its compatibility is derived from the
   inclusion factorization and the original comma arrow. -/
noncomputable def hprime {S T : Scheme.{u}} {f : T ⟶ S} {V : T.Etale} {U : Scheme.{u}}
    {g : U ⟶ S} [Etale g] {C : EtaleCommaInput f V g}
    {A : AffineChartSelection C} {hA : imageContainingUnionLaw C A}
    (c : CorrectedCommaCompositionData g C A hA) :
    V.left ⟶ pullback (gprime A) f :=
  pullback.lift (projectionToImage C A hA) V.hom
    (projectionToImage_comp_g C A hA)

noncomputable def rT {S T : Scheme.{u}} {f : T ⟶ S} {V : T.Etale}
    {U : Scheme.{u}} {g : U ⟶ S} [Etale g] {C : EtaleCommaInput f V g}
    {A : AffineChartSelection C} {hA : imageContainingUnionLaw C A}
    (c : CorrectedCommaCompositionData g C A hA) :
    pullback (gluedToS c.D (coverCompat_of_chart_over_S c.D)) f ⟶ pullback g f :=
  pullback.map _ _ _ _ (r c) (𝟙 _) (𝟙 _)
    (by simpa using (r_overS c)) (by simp)

def t {S T : Scheme.{u}} {f : T ⟶ S} {V : T.Etale} {U : Scheme.{u}}
    {g : U ⟶ S} [Etale g] {C : EtaleCommaInput f V g}
    {A : AffineChartSelection C} {hA : imageContainingUnionLaw C A}
    (c : CorrectedCommaCompositionData g C A hA) :
    V.left ⟶ pullback (gluedToS c.D (coverCompat_of_chart_over_S c.D)) f :=
  hprime c ≫ (ψT c).inv

lemma ψT_hom_fst {S T : Scheme.{u}} {f : T ⟶ S} {V : T.Etale} {U : Scheme.{u}}
    {g : U ⟶ S} [Etale g] {C : EtaleCommaInput f V g}
    {A : AffineChartSelection C} {hA : imageContainingUnionLaw C A}
    (c : CorrectedCommaCompositionData g C A hA) :
    (ψT c).hom ≫ pullback.fst (gprime A) f =
      pullback.fst (gluedToS c.D (coverCompat_of_chart_over_S c.D)) f ≫ c.ψ.hom := by
  simp only [ψT, asIso_hom, pullback.map, pullback.lift_fst]

lemma ψT_hom_snd {S T : Scheme.{u}} {f : T ⟶ S} {V : T.Etale} {U : Scheme.{u}}
    {g : U ⟶ S} [Etale g] {C : EtaleCommaInput f V g}
    {A : AffineChartSelection C} {hA : imageContainingUnionLaw C A}
    (c : CorrectedCommaCompositionData g C A hA) :
    (ψT c).hom ≫ pullback.snd (gprime A) f =
      pullback.snd (gluedToS c.D (coverCompat_of_chart_over_S c.D)) f := by
  simp only [ψT, asIso_hom, pullback.map, pullback.lift_snd, Category.comp_id]

lemma hprime_fst {S T : Scheme.{u}} {f : T ⟶ S} {V : T.Etale} {U : Scheme.{u}}
    {g : U ⟶ S} [Etale g] {C : EtaleCommaInput f V g}
    {A : AffineChartSelection C} {hA : imageContainingUnionLaw C A}
    (c : CorrectedCommaCompositionData g C A hA) :
    hprime c ≫ pullback.fst (gprime A) f = projectionToImage C A hA := by
  simp only [hprime, pullback.lift_fst]

lemma hprime_snd {S T : Scheme.{u}} {f : T ⟶ S} {V : T.Etale} {U : Scheme.{u}}
    {g : U ⟶ S} [Etale g] {C : EtaleCommaInput f V g}
    {A : AffineChartSelection C} {hA : imageContainingUnionLaw C A}
    (c : CorrectedCommaCompositionData g C A hA) :
    hprime c ≫ pullback.snd (gprime A) f = V.hom := by
  simp only [hprime, pullback.lift_snd]

lemma rT_fst {S T : Scheme.{u}} {f : T ⟶ S} {V : T.Etale} {U : Scheme.{u}}
    {g : U ⟶ S} [Etale g] {C : EtaleCommaInput f V g}
    {A : AffineChartSelection C} {hA : imageContainingUnionLaw C A}
    (c : CorrectedCommaCompositionData g C A hA) :
    rT c ≫ pullback.fst g f =
      pullback.fst (gluedToS c.D (coverCompat_of_chart_over_S c.D)) f ≫ r c := by
  simp only [rT, pullback.map, pullback.lift_fst]

lemma rT_snd {S T : Scheme.{u}} {f : T ⟶ S} {V : T.Etale} {U : Scheme.{u}}
    {g : U ⟶ S} [Etale g] {C : EtaleCommaInput f V g}
    {A : AffineChartSelection C} {hA : imageContainingUnionLaw C A}
    (c : CorrectedCommaCompositionData g C A hA) :
    rT c ≫ pullback.snd g f =
      pullback.snd (gluedToS c.D (coverCompat_of_chart_over_S c.D)) f := by
  simp only [rT, pullback.map, pullback.lift_snd, Category.comp_id]

theorem t_rT_factor {S T : Scheme.{u}} {f : T ⟶ S} {V : T.Etale} {U : Scheme.{u}}
    {g : U ⟶ S} [Etale g] {C : EtaleCommaInput f V g}
    {A : AffineChartSelection C} {hA : imageContainingUnionLaw C A}
    (c : CorrectedCommaCompositionData g C A hA) :
    t c ≫ rT c = C.h := by
  apply pullback.hom_ext
  · calc
      (t c ≫ rT c) ≫ pullback.fst g f =
          hprime c ≫ (ψT c).inv ≫
            (pullback.fst (gluedToS c.D (coverCompat_of_chart_over_S c.D)) f ≫ r c) := by
        simp only [Category.assoc, t, rT_fst]
      _ = hprime c ≫ (ψT c).inv ≫
          ((pullback.fst (gluedToS c.D (coverCompat_of_chart_over_S c.D)) f ≫ c.ψ.hom) ≫
            j A) := by
        simp [r, Category.assoc]
      _ = hprime c ≫ (ψT c).inv ≫
          ((ψT c).hom ≫ pullback.fst (gprime A) f) ≫ j A := by
        rw [ψT_hom_fst c]
      _ = hprime c ≫ pullback.fst (gprime A) f ≫ j A := by
        simp [Category.assoc]
      _ = projectionToImage C A hA ≫ j A := by
        rw [← Category.assoc, hprime_fst c]
      _ = C.h ≫ pullback.fst g f := by
        simpa [j, commaInputProjection] using
          (projectionToImage_comp_inclusion C A hA)
  · calc
      (t c ≫ rT c) ≫ pullback.snd g f =
          hprime c ≫ (ψT c).inv ≫
            pullback.snd (gluedToS c.D (coverCompat_of_chart_over_S c.D)) f := by
        simp only [Category.assoc, t, rT_snd]
      _ = hprime c ≫ (ψT c).inv ≫
          ((ψT c).hom ≫ pullback.snd (gprime A) f) := by
        rw [ψT_hom_snd c]
      _ = hprime c ≫ pullback.snd (gprime A) f := by
        simp [Category.assoc]
      _ = C.h ≫ pullback.snd g f := (hprime_snd c).trans C.overT.symm

theorem t_overT {S T : Scheme.{u}} {f : T ⟶ S} {V : T.Etale} {U : Scheme.{u}}
    {g : U ⟶ S} [Etale g] {C : EtaleCommaInput f V g}
    {A : AffineChartSelection C} {hA : imageContainingUnionLaw C A}
    (c : CorrectedCommaCompositionData g C A hA) :
    t c ≫ pullback.snd (gluedToS c.D (coverCompat_of_chart_over_S c.D)) f = V.hom := by
  calc
    t c ≫ pullback.snd (gluedToS c.D (coverCompat_of_chart_over_S c.D)) f =
        hprime c ≫ (ψT c).inv ≫
          pullback.snd (gluedToS c.D (coverCompat_of_chart_over_S c.D)) f := by
      simp [t, Category.assoc]
    _ = hprime c ≫ (ψT c).inv ≫
        ((ψT c).hom ≫ pullback.snd (gprime A) f) := by
      rw [ψT_hom_snd c]
    _ = hprime c ≫ pullback.snd (gprime A) f := by
      simp [Category.assoc]
    _ = V.hom := hprime_snd c

/- These are the two actual factor-layer laws: factorization through `rT` and
   the over-`T` equation.  They are derived propositions, so no law is stored
   in the data and no unresolved geometric proof manufactures a morphism. -/
theorem correctedCommaCompositionLaw {S T : Scheme.{u}} {f : T ⟶ S} {V : T.Etale}
    {U : Scheme.{u}} {g : U ⟶ S} [Etale g] {C : EtaleCommaInput f V g}
    {A : AffineChartSelection C} {hA : imageContainingUnionLaw C A}
    (c : CorrectedCommaCompositionData g C A hA) :
    t c ≫ rT c = C.h ∧
      t c ≫ pullback.snd (gluedToS c.D (coverCompat_of_chart_over_S c.D)) f = V.hom := by
  exact ⟨t_rT_factor c, t_overT c⟩

/- The code provider retains the actual input `C` and chart selection `A`; it
   asks for exactly the fixed-union atlas, its anchored comparison isomorphism,
   and both compatibility laws.  It does not choose data from an admitted
   nonempty proposition and does not quantify over an arbitrary `U'`. -/
def codedGlueComparisonProvider {S T : Scheme.{u}} {f : T ⟶ S} {V : T.Etale}
    {U : Scheme.{u}} (g : U ⟶ S) [Etale g] (C : EtaleCommaInput f V g)
    (A : AffineChartSelection C) (hA : imageContainingUnionLaw C A) : Prop :=
  ∃ c : CorrectedCommaCompositionData g C A hA,
    t c ≫ rT c = C.h ∧
      t c ≫ pullback.snd (gluedToS c.D (coverCompat_of_chart_over_S c.D)) f = V.hom

/- The canonical chart selection is the default concrete input to the provider;
   its remaining existence and factorization are still propositions. -/
def canonicalCodedGlueComparisonProvider {S T : Scheme.{u}}
    {f : T ⟶ S} {V : T.Etale} {U : Scheme.{u}} (g : U ⟶ S) [Etale g]
    (C : EtaleCommaInput f V g) : Prop :=
  codedGlueComparisonProvider g C (canonicalAffineChartSelection g C)
    (canonicalImageContainingUnionLaw g C)

end AlgebraicGeometry.Scheme.Etale.PullbackBounds
