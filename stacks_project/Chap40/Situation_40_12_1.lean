/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Restriction.Fiber
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.Stabilizer.Immersion

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

variable {S : Scheme.{u}} (G : GroupoidScheme S) {U' : Over S}

/- Situation 40.12.1 (1): the stabilizer of a groupoid scheme is canonically a group
scheme over its object scheme. -/
@[stacks 04MY] #check
  (AlgebraicGeometry.GroupoidScheme.stabilizer G : Grp (Over G.U))

/- Situation 40.12.1 (2): the stabilizer is a locally closed subscheme of the arrow
scheme. -/
@[stacks 04MY] #check
  (AlgebraicGeometry.Scheme.PreRelation.isImmersion_stabilizerToArrows G.toPreRelation :
    IsImmersion G.toPreRelation.stabilizerToArrows.left)

/- Situation 40.12.1 (3): the map
`h : U' ×_{g, G.U, G.t} G.R ⟶ G.U` is the second projection followed by the source map. -/
@[stacks 04MY] #check
  (AlgebraicGeometry.GroupoidScheme.saturationMap_def G :
    ∀ g : U' ⟶ G.U,
      AlgebraicGeometry.GroupoidScheme.saturationMap G g =
        Limits.pullback.snd g G.t ≫ G.s)

#check
  (AlgebraicGeometry.GroupoidScheme.saturationMap G :
    (g : U' ⟶ G.U) → Limits.pullback g G.t ⟶ G.U)

/- Situation 40.12.1 (4): the source fibre of the restricted groupoid is the
residue-field base change of the fibre of `saturationMap G g` at `g.left u'`. -/
@[stacks 04MY] #check
  (AlgebraicGeometry.GroupoidScheme.sliceFiberMap_isPullback G :
    ∀ (g : U' ⟶ G.U) (u' : U'.left),
      IsPullback (AlgebraicGeometry.GroupoidScheme.sliceFiberMap G g u')
        ((G.pullback g).s.left.fiberToSpecResidueField u')
        ((AlgebraicGeometry.GroupoidScheme.saturationMap G g).left.fiberToSpecResidueField
          (g.left u'))
        (Spec.map (g.left.residueFieldMap u')))

#check
  (AlgebraicGeometry.GroupoidScheme.sliceFiberMap G :
    (g : U' ⟶ G.U) → (u' : U'.left) →
      (G.pullback g).s.left.fiber u' ⟶
        (AlgebraicGeometry.GroupoidScheme.saturationMap G g).left.fiber (g.left u'))

/- Situation 40.12.1 (5): the identity arrow `G.e(u)` as a point of the
scheme-theoretic source fibre at `u`. -/
@[stacks 04MY] #check
  (AlgebraicGeometry.GroupoidScheme.sourceFiberUnit_fiberι G :
    ∀ u : G.U.left,
      Scheme.Hom.fiberι G.s.left u
          (AlgebraicGeometry.GroupoidScheme.sourceFiberUnit G u) =
        G.e.left u)

#check
  (AlgebraicGeometry.GroupoidScheme.sourceFiberUnit G :
    (u : G.U.left) → Scheme.Hom.fiber G.s.left u)

/- Situation 40.12.1 (6): the identity arrow `G.e(u)` as a point of the
scheme-theoretic stabilizer fibre at `u`. -/
@[stacks 04MY] #check
  (AlgebraicGeometry.GroupoidScheme.stabilizerFiberUnit_toArrows G :
    ∀ u : G.U.left,
      (PreRelation.stabilizerToArrows G.toPreRelation).left
          (Scheme.Hom.fiberι (PreRelation.stabilizer G.toPreRelation).hom.left u
            (AlgebraicGeometry.GroupoidScheme.stabilizerFiberUnit G u)) =
        G.e.left u)

#check
  (AlgebraicGeometry.GroupoidScheme.stabilizerFiberUnit G :
    (u : G.U.left) →
      Scheme.Hom.fiber (PreRelation.stabilizer G.toPreRelation).hom.left u)

/- Situation 40.12.1 (7): the restriction map sends the restricted identity arrow at
`u'` to the original identity arrow at `g.left u'`. -/
@[stacks 04MY] #check
  (AlgebraicGeometry.GroupoidScheme.restrictionArrow_unit G :
    ∀ (g : U' ⟶ G.U) (u' : U'.left),
      (pullbackHom G g).arrow.left ((G.pullback g).e.left u') =
        G.e.left (g.left u'))

/- Situation 40.12.1 (8): the restricted source-fibre identity point maps to the
original source-fibre identity point. -/
@[stacks 04MY] #check
  (AlgebraicGeometry.GroupoidScheme.sourceFiberMap_unit G :
    ∀ (g : U' ⟶ G.U) (u' : U'.left),
      AlgebraicGeometry.GroupoidScheme.sourceFiberMap G g u'
          (AlgebraicGeometry.GroupoidScheme.sourceFiberUnit (G.pullback g) u') =
        AlgebraicGeometry.GroupoidScheme.sourceFiberUnit G (g.left u'))

#check
  (AlgebraicGeometry.GroupoidScheme.sourceFiberMap G :
    (g : U' ⟶ G.U) → (u' : U'.left) →
      Scheme.Hom.fiber (G.pullback g).s.left u' ⟶
        Scheme.Hom.fiber G.s.left (g.left u'))

/- Situation 40.12.1 (9): the restricted stabilizer-fibre identity point maps to the
original stabilizer-fibre identity point. -/
@[stacks 04MY] #check
  (AlgebraicGeometry.GroupoidScheme.stabilizerFiberMap_unit G :
    ∀ (g : U' ⟶ G.U) (u' : U'.left),
      AlgebraicGeometry.GroupoidScheme.stabilizerFiberMap G g u'
          (AlgebraicGeometry.GroupoidScheme.stabilizerFiberUnit (G.pullback g) u') =
        AlgebraicGeometry.GroupoidScheme.stabilizerFiberUnit G (g.left u'))

#check
  (AlgebraicGeometry.GroupoidScheme.stabilizerFiberMap G :
    (g : U' ⟶ G.U) → (u' : U'.left) →
      Scheme.Hom.fiber
          (PreRelation.stabilizer (G.pullback g).toPreRelation).hom.left u' ⟶
        Scheme.Hom.fiber (PreRelation.stabilizer G.toPreRelation).hom.left
          (g.left u'))

end AlgebraicGeometry.GroupoidScheme
