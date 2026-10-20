module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Stabilizer

/-!
# Inertia presentation of a groupoid in algebraic spaces

This module constructs the groupoid `(G, R', s', t', c')` in algebraic spaces over `B`
associated to the stabilizer of a groupoid `(U, R, s, t, c)`. The arrow space is the
pullback `R ×_{s,U} G`, source is the second projection, target is conjugation
`c(r, c(g, i(r)))`, and composition sends a composable pair to
`(c(later, earlier), s'(earlier))`.
-/

@[expose] public section

-- Local declaration justification (module visibility): exposed pullback and over-category
-- constructions reference private compatibility proof arguments. Their computational maps
-- remain explicit; this option only permits those private proof dependencies.
set_option backward.privateInPublic true

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- The arrow space `R' = R ×_{s, U} G` of the inertia presentation. -/
def inertiaArrows {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    Over B :=
  pullback G.s G.toPreRelation.stabilizer.hom

/-- The source map `s' : R' ⟶ G` of the inertia presentation, `(r, g) ↦ g`. -/
def inertiaSource {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    inertiaArrows G ⟶ G.toPreRelation.stabilizer.left :=
  pullback.snd G.s G.toPreRelation.stabilizer.hom

/-- The source map of the inertia presentation is the second pullback projection. -/
theorem inertiaSource_eq_snd {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    inertiaSource G = pullback.snd G.s G.toPreRelation.stabilizer.hom :=
  sorry

/-- The inner composite `c(g, i(r))` used by conjugation is well-defined. -/
private theorem inertiaConjugationInner_condition {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    ((pullback.snd G.s G.toPreRelation.stabilizer.hom ≫
          G.toPreRelation.stabilizerToArrows) ≫ G.s) =
      ((pullback.fst G.s G.toPreRelation.stabilizer.hom ≫ G.i) ≫ G.t) :=
  sorry

/-- The inner composite `c(g, i(r))` of a pair `(r, g)` in `R'`. -/
def inertiaConjugationInner {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) : inertiaArrows G ⟶ G.R :=
  G.compose
    (pullback.snd G.s G.toPreRelation.stabilizer.hom ≫
      G.toPreRelation.stabilizerToArrows)
    (pullback.fst G.s G.toPreRelation.stabilizer.hom ≫ G.i)
    (inertiaConjugationInner_condition G)

/-- The outer composite `c(r, c(g, i(r)))` is well-defined. -/
private theorem inertiaConjugation_condition {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    (pullback.fst G.s G.toPreRelation.stabilizer.hom ≫ G.s) =
      inertiaConjugationInner G ≫ G.t :=
  sorry

/-- The conjugation arrow `c(r, c(g, i(r)))` of a pair `(r, g)` in `R'`. -/
def inertiaConjugation {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) : inertiaArrows G ⟶ G.R :=
  G.compose (pullback.fst G.s G.toPreRelation.stabilizer.hom)
    (inertiaConjugationInner G) (inertiaConjugation_condition G)

/-- Conjugation lands in the stabilizer of the original groupoid. -/
private theorem inertiaTarget_condition {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    inertiaConjugation G ≫ G.toPreRelation.hom =
      (pullback.fst G.s G.toPreRelation.stabilizer.hom ≫ G.t) ≫ diag G.U :=
  sorry

/-- The target map `t' : R' ⟶ G` of the inertia presentation,
`(r, g) ↦ c(r, c(g, i(r)))`. -/
def inertiaTarget {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    inertiaArrows G ⟶ G.toPreRelation.stabilizer.left :=
  pullback.lift (inertiaConjugation G)
    (pullback.fst G.s G.toPreRelation.stabilizer.hom ≫ G.t)
    (inertiaTarget_condition G)

/-- The target map of the inertia presentation is conjugation as an arrow of `R`. -/
theorem inertiaTarget_toArrows {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    inertiaTarget G ≫ G.toPreRelation.stabilizerToArrows = inertiaConjugation G :=
  sorry

/-- Later and earlier `R`-components of a composable pair in `R'` are composable. -/
private theorem inertiaComposition_pair_condition {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    ((pullback.fst (inertiaSource G) (inertiaTarget G) ≫
          pullback.fst G.s G.toPreRelation.stabilizer.hom) ≫ G.s) =
      ((pullback.snd (inertiaSource G) (inertiaTarget G) ≫
          pullback.fst G.s G.toPreRelation.stabilizer.hom) ≫ G.t) :=
  sorry

/-- The `R`-component of a composite in the inertia presentation, together with the
source of the earlier arrow, defines a point of `R'`. -/
private theorem inertiaComposition_condition {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    (G.compose
          (pullback.fst (inertiaSource G) (inertiaTarget G) ≫
            pullback.fst G.s G.toPreRelation.stabilizer.hom)
          (pullback.snd (inertiaSource G) (inertiaTarget G) ≫
            pullback.fst G.s G.toPreRelation.stabilizer.hom)
          (inertiaComposition_pair_condition G) ≫ G.s) =
      ((pullback.snd (inertiaSource G) (inertiaTarget G) ≫ inertiaSource G) ≫
        G.toPreRelation.stabilizer.hom) :=
  sorry

/-- The composition map `c'` of the inertia presentation,
`((later, g_later), (earlier, g_earlier)) ↦ (c(later, earlier), g_earlier)`. -/
def inertiaComposition {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    pullback (inertiaSource G) (inertiaTarget G) ⟶ inertiaArrows G :=
  pullback.lift
    (G.compose
      (pullback.fst (inertiaSource G) (inertiaTarget G) ≫
        pullback.fst G.s G.toPreRelation.stabilizer.hom)
      (pullback.snd (inertiaSource G) (inertiaTarget G) ≫
        pullback.fst G.s G.toPreRelation.stabilizer.hom)
      (inertiaComposition_pair_condition G))
    (pullback.snd (inertiaSource G) (inertiaTarget G) ≫ inertiaSource G)
    (inertiaComposition_condition G)

/-- The first projection of `inertiaComposition` is groupoid composition of the
underlying arrows. -/
theorem inertiaComposition_fst {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    inertiaComposition G ≫ pullback.fst G.s G.toPreRelation.stabilizer.hom =
      G.compose
        (pullback.fst (inertiaSource G) (inertiaTarget G) ≫
          pullback.fst G.s G.toPreRelation.stabilizer.hom)
        (pullback.snd (inertiaSource G) (inertiaTarget G) ≫
          pullback.fst G.s G.toPreRelation.stabilizer.hom)
        (inertiaComposition_pair_condition G) :=
  sorry

/-- The second projection of `inertiaComposition` is the source of the earlier arrow. -/
theorem inertiaComposition_snd {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    inertiaComposition G ≫ inertiaSource G =
      pullback.snd (inertiaSource G) (inertiaTarget G) ≫ inertiaSource G :=
  sorry

/-- The identity arrow `g ↦ (e(π(g)), g)` of the inertia presentation is well-defined. -/
private theorem inertiaIdentity_condition {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    ((G.toPreRelation.stabilizer.hom ≫ G.e) ≫ G.s) =
      𝟙 G.toPreRelation.stabilizer.left ≫ G.toPreRelation.stabilizer.hom :=
  sorry

/-- The identity map of the inertia presentation, `g ↦ (e(π(g)), g)`. -/
def inertiaIdentity {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    G.toPreRelation.stabilizer.left ⟶ inertiaArrows G :=
  pullback.lift (G.toPreRelation.stabilizer.hom ≫ G.e) (𝟙 _)
    (inertiaIdentity_condition G)

/-- The inverse arrow `(r, g) ↦ (i(r), t'(r, g))` of the inertia presentation is
well-defined. -/
private theorem inertiaInverse_condition {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    ((pullback.fst G.s G.toPreRelation.stabilizer.hom ≫ G.i) ≫ G.s) =
      inertiaTarget G ≫ G.toPreRelation.stabilizer.hom :=
  sorry

/-- The inverse map of the inertia presentation, `(r, g) ↦ (i(r), t'(r, g))`. -/
def inertiaInverse {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) : inertiaArrows G ⟶ inertiaArrows G :=
  pullback.lift (pullback.fst G.s G.toPreRelation.stabilizer.hom ≫ G.i)
    (inertiaTarget G) (inertiaInverse_condition G)

/-- The groupoid in algebraic spaces over `B` with object space the stabilizer `G`,
arrow space `R' = R ×_{s, U} G`, source `(r, g) ↦ g`, target
`(r, g) ↦ c(r, c(g, i(r)))`, and composition
`((later, g_later), (earlier, g_earlier)) ↦ (c(later, earlier), g_earlier)`. -/
def inertiaPresentation {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) : GroupoidAlgebraicSpace B where
  U := G.toPreRelation.stabilizer.left
  R := inertiaArrows G
  s := inertiaSource G
  t := inertiaTarget G
  c := inertiaComposition G
  e := inertiaIdentity G
  i := inertiaInverse G
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

/-- The object space of the inertia presentation is the stabilizer. -/
theorem inertiaPresentation_U {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    (inertiaPresentation G).U = G.toPreRelation.stabilizer.left :=
  sorry

/-- The arrow space of the inertia presentation is `R ×_{s, U} G`. -/
theorem inertiaPresentation_R {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    (inertiaPresentation G).R = inertiaArrows G :=
  sorry

/-- The source map of the inertia presentation is `s'`. -/
theorem inertiaPresentation_s {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    (inertiaPresentation G).s = inertiaSource G :=
  sorry

/-- The target map of the inertia presentation is `t'`. -/
theorem inertiaPresentation_t {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    (inertiaPresentation G).t = inertiaTarget G :=
  sorry

/-- The composition map of the inertia presentation is `c'`. -/
theorem inertiaPresentation_c {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    (inertiaPresentation G).c = inertiaComposition G :=
  sorry

/-- The identity map of the inertia presentation inserts `e(π(g))`. -/
theorem inertiaPresentation_e {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    (inertiaPresentation G).e = inertiaIdentity G :=
  sorry

/-- The inverse map of the inertia presentation is `(r, g) ↦ (i(r), t'(r, g))`. -/
theorem inertiaPresentation_i {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    (inertiaPresentation G).i = inertiaInverse G :=
  sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
