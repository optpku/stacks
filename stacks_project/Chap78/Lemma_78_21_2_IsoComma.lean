/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap78.Definition_78_11_1_Groupoid

/-!
# Iso-comma groupoid of a morphism of groupoids in algebraic spaces

A morphism `f : Hom G H` determines a groupoid `(U'', R'', s'', t'', c'')` over the same base
`B`, with object space the pullback of `f.obj` along `H.t` and arrow space the pullback of
`G.s ≫ f.obj` along `H.t`. The first projections supply a morphism `g` to `G`, and the source
of the `R'`-factor supplies the structure map `U'' ⟶ U'`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace.Hom

variable {S : Scheme.{u}} {B : AlgebraicSpace S} {G H : GroupoidAlgebraicSpace B}

/-- The object space `U'' = U ×_{f, U', t'} R'` of the iso-comma groupoid. -/
def isoCommaObject (f : Hom G H) : Over B :=
  pullback f.obj H.t

/-- The arrow space `R'' = R ×_{f ∘ s, U', t'} R'` of the iso-comma groupoid. -/
def isoCommaArrow (f : Hom G H) : Over B :=
  pullback (G.s ≫ f.obj) H.t

/-- The first projection of `U''` lands over `U'` after applying `f`. -/
theorem isoCommaObject_condition (f : Hom G H) :
    pullback.fst f.obj H.t ≫ f.obj = pullback.snd f.obj H.t ≫ H.t := sorry

/-- The first projection of `R''` lands over `U'` after applying `f ∘ s`. -/
theorem isoCommaArrow_condition (f : Hom G H) :
    pullback.fst (G.s ≫ f.obj) H.t ≫ G.s ≫ f.obj =
      pullback.snd (G.s ≫ f.obj) H.t ≫ H.t := sorry

/-- The `R'`-factor of an `R''`-point is composable after `f` with source `f(s(r))`. -/
theorem isoComma_compose_condition (f : Hom G H) :
    pullback.fst (G.s ≫ f.obj) H.t ≫ f.arrow ≫ H.s =
      pullback.snd (G.s ≫ f.obj) H.t ≫ H.t := sorry

/-- Source compatibility for `s''(r, r') = (s(r), r')`. -/
theorem isoCommaSource_w (f : Hom G H) :
    (pullback.fst (G.s ≫ f.obj) H.t ≫ G.s) ≫ f.obj =
      pullback.snd (G.s ≫ f.obj) H.t ≫ H.t := sorry

/-- The source map `s'' : R'' ⟶ U''`, `(r, r') ↦ (s(r), r')`. -/
def isoCommaSource (f : Hom G H) : isoCommaArrow f ⟶ isoCommaObject f :=
  pullback.lift (pullback.fst (G.s ≫ f.obj) H.t ≫ G.s)
    (pullback.snd (G.s ≫ f.obj) H.t) (isoCommaSource_w f)

/-- The composite `c'(f(r), r')` used by `t''` and `i''`. -/
def isoCommaTargetArrow (f : Hom G H) : isoCommaArrow f ⟶ H.R :=
  H.compose (pullback.fst (G.s ≫ f.obj) H.t ≫ f.arrow)
    (pullback.snd (G.s ≫ f.obj) H.t) (isoComma_compose_condition f)

/-- Target compatibility for `t''(r, r') = (t(r), c'(f(r), r'))`. -/
theorem isoCommaTarget_w (f : Hom G H) :
    (pullback.fst (G.s ≫ f.obj) H.t ≫ G.t) ≫ f.obj =
      isoCommaTargetArrow f ≫ H.t := sorry

/-- The target map `t'' : R'' ⟶ U''`, `(r, r') ↦ (t(r), c'(f(r), r'))`. -/
def isoCommaTarget (f : Hom G H) : isoCommaArrow f ⟶ isoCommaObject f :=
  pullback.lift (pullback.fst (G.s ≫ f.obj) H.t ≫ G.t)
    (isoCommaTargetArrow f) (isoCommaTarget_w f)

/-- The later `G`-arrow of a composable pair in `R''`. -/
def isoCommaLater (f : Hom G H) :
    pullback (isoCommaSource f) (isoCommaTarget f) ⟶ G.R :=
  pullback.fst (isoCommaSource f) (isoCommaTarget f) ≫
    pullback.fst (G.s ≫ f.obj) H.t

/-- The earlier `G`-arrow of a composable pair in `R''`. -/
def isoCommaEarlier (f : Hom G H) :
    pullback (isoCommaSource f) (isoCommaTarget f) ⟶ G.R :=
  pullback.snd (isoCommaSource f) (isoCommaTarget f) ≫
    pullback.fst (G.s ≫ f.obj) H.t

/-- The earlier `R'`-factor of a composable pair in `R''`. -/
def isoCommaEarlierFactor (f : Hom G H) :
    pullback (isoCommaSource f) (isoCommaTarget f) ⟶ H.R :=
  pullback.snd (isoCommaSource f) (isoCommaTarget f) ≫
    pullback.snd (G.s ≫ f.obj) H.t

/-- Composability of the two `G`-arrows in a composable pair of `R''`. -/
theorem isoCommaComp_arrows (f : Hom G H) :
    isoCommaLater f ≫ G.s = isoCommaEarlier f ≫ G.t := sorry

/-- The composite `G`-arrow of a composable pair in `R''`. -/
def isoCommaCompArrow (f : Hom G H) :
    pullback (isoCommaSource f) (isoCommaTarget f) ⟶ G.R :=
  G.compose (isoCommaLater f) (isoCommaEarlier f) (isoCommaComp_arrows f)

/-- Composition compatibility for `c''((r₁, r'₁), (r₂, r'₂)) = (c(r₁, r₂), r'₂)`. -/
theorem isoCommaComp_w (f : Hom G H) :
    isoCommaCompArrow f ≫ G.s ≫ f.obj = isoCommaEarlierFactor f ≫ H.t := sorry

/-- The composition map `c''` of the iso-comma groupoid. -/
def isoCommaComp (f : Hom G H) :
    pullback (isoCommaSource f) (isoCommaTarget f) ⟶ isoCommaArrow f :=
  pullback.lift (isoCommaCompArrow f) (isoCommaEarlierFactor f) (isoCommaComp_w f)

/-- Identity compatibility for `e''(u, r') = (e(u), r')`. -/
theorem isoCommaId_w (f : Hom G H) :
    (pullback.fst f.obj H.t ≫ G.e) ≫ G.s ≫ f.obj =
      pullback.snd f.obj H.t ≫ H.t := sorry

/-- The identity-arrow map `e'' : U'' ⟶ R''`, `(u, r') ↦ (e(u), r')`. -/
def isoCommaId (f : Hom G H) : isoCommaObject f ⟶ isoCommaArrow f :=
  pullback.lift (pullback.fst f.obj H.t ≫ G.e) (pullback.snd f.obj H.t)
    (isoCommaId_w f)

/-- Inverse compatibility for `i''(r, r') = (i(r), c'(f(r), r'))`. -/
theorem isoCommaInv_w (f : Hom G H) :
    (pullback.fst (G.s ≫ f.obj) H.t ≫ G.i) ≫ G.s ≫ f.obj =
      isoCommaTargetArrow f ≫ H.t := sorry

/-- The inverse-arrow map `i'' : R'' ⟶ R''`, `(r, r') ↦ (i(r), c'(f(r), r'))`. -/
def isoCommaInv (f : Hom G H) : isoCommaArrow f ⟶ isoCommaArrow f :=
  pullback.lift (pullback.fst (G.s ≫ f.obj) H.t ≫ G.i) (isoCommaTargetArrow f)
    (isoCommaInv_w f)

/-- The iso-comma groupoid `(U'', R'', s'', t'', c'')` associated to a morphism of groupoids
in algebraic spaces over `B`. -/
def isoComma (f : Hom G H) : GroupoidAlgebraicSpace B where
  U := isoCommaObject f
  R := isoCommaArrow f
  s := isoCommaSource f
  t := isoCommaTarget f
  c := isoCommaComp f
  e := isoCommaId f
  i := isoCommaInv f
  comp_source := sorry
  comp_target := sorry
  identity_source := sorry
  identity_target := sorry
  inverse_source := sorry
  inverse_target := sorry
  associativity := sorry
  right_identity := sorry
  left_identity := sorry
  inverse_comp := sorry
  comp_inverse := sorry

/-- The object space of the iso-comma groupoid is `U ×_{f, U', t'} R'`. -/
theorem isoComma_U (f : Hom G H) : (isoComma f).U = pullback f.obj H.t := sorry

/-- The arrow space of the iso-comma groupoid is `R ×_{f ∘ s, U', t'} R'`. -/
theorem isoComma_R (f : Hom G H) : (isoComma f).R = pullback (G.s ≫ f.obj) H.t := sorry

/-- The source map of the iso-comma groupoid is `s''(r, r') = (s(r), r')`. -/
theorem isoComma_s (f : Hom G H) : (isoComma f).s = isoCommaSource f := sorry

/-- The target map of the iso-comma groupoid is `t''(r, r') = (t(r), c'(f(r), r'))`. -/
theorem isoComma_t (f : Hom G H) : (isoComma f).t = isoCommaTarget f := sorry

/-- The composition map of the iso-comma groupoid is `c''((r₁, r'₁), (r₂, r'₂)) = (c(r₁, r₂), r'₂)`. -/
theorem isoComma_c (f : Hom G H) : (isoComma f).c = isoCommaComp f := sorry

/-- The identity map of the iso-comma groupoid is `e''(u, r') = (e(u), r')`. -/
theorem isoComma_e (f : Hom G H) : (isoComma f).e = isoCommaId f := sorry

/-- The inverse map of the iso-comma groupoid is `i''(r, r') = (i(r), c'(f(r), r'))`. -/
theorem isoComma_i (f : Hom G H) : (isoComma f).i = isoCommaInv f := sorry

/-- The morphism `g : G'' ⟶ G` of groupoids over `B` given by the first projections
`U'' ⟶ U` and `R'' ⟶ R`. -/
def isoCommaHom (f : Hom G H) : Hom (isoComma f) G where
  obj := pullback.fst f.obj H.t
  arrow := pullback.fst (G.s ≫ f.obj) H.t
  map_s := sorry
  map_t := sorry
  map_c := sorry

/-- The object component of `g` is the first projection of `U''`. -/
theorem isoCommaHom_obj (f : Hom G H) :
    (isoCommaHom f).obj = pullback.fst f.obj H.t := sorry

/-- The arrow component of `g` is the first projection of `R''`. -/
theorem isoCommaHom_arrow (f : Hom G H) :
    (isoCommaHom f).arrow = pullback.fst (G.s ≫ f.obj) H.t := sorry

/-- The structure map `U'' ⟶ U'` sending `(u, r')` to `s'(r')`. -/
def isoCommaToTargetObject (f : Hom G H) : (isoComma f).U ⟶ H.U :=
  pullback.snd f.obj H.t ≫ H.s

/-- The left component of `U'' ⟶ U'` is `s'` of the `R'`-factor. -/
theorem isoCommaToTargetObject_left (f : Hom G H) :
    (isoCommaToTargetObject f).left =
      (pullback.snd f.obj H.t).left ≫ H.s.left := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace.Hom
