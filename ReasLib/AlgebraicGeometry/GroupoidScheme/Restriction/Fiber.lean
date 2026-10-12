/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Restriction.Presentation
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Stabilizer.Morphism
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.BaseChange

/-!
# Fibres of restricted groupoid schemes

This module constructs the slicing source morphism associated to a restriction of a groupoid
scheme, compares its fixed fibres with those of the restricted source, and records the behaviour
of the distinguished identity points in source and stabilizer fibres.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- The slicing source morphism is the second projection from the target pullback followed by
the groupoid source map. -/
def sliceSource {S : Scheme.{u}} (G : GroupoidScheme S) {U' : Over S}
    (g : U' ⟶ G.U) : Limits.pullback g G.t ⟶ G.U :=
  Limits.pullback.snd g G.t ≫ G.s

/-- The slicing source map is the second projection followed by the groupoid source. -/
theorem sliceSource_def {S : Scheme.{u}} (G : GroupoidScheme S) {U' : Over S}
    (g : U' ⟶ G.U) :
    sliceSource G g = Limits.pullback.snd g G.t ≫ G.s := sorry

/-- The restricted source map is the pullback of the slicing source map along `g`. -/
theorem restrictionSourceSquare {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U) :
    IsPullback (pullbackToTargetSquare G g).left (G.pullback g).s.left
      (sliceSource G g).left g.left := sorry

/-- The canonical map from the restricted source fibre to the corresponding fibre of the
slicing source map. -/
def sliceFiberMap {S : Scheme.{u}} (G : GroupoidScheme S) {U' : Over S}
    (g : U' ⟶ G.U) (u' : U'.left) :
    (G.pullback g).s.left.fiber u' ⟶ (sliceSource G g).left.fiber (g.left u') :=
  Scheme.Hom.baseChangeFiberMap (sliceSource G g).left g.left
    (pullbackToTargetSquare G g).left (G.pullback g).s.left
    (restrictionSourceSquare G g) u'

/-- The slicing fibre map is compatible with the maps to the restricted and original
arrow schemes. -/
theorem sliceFiberMap_fiberι {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U) (u' : U'.left) :
    sliceFiberMap G g u' ≫ (sliceSource G g).left.fiberι (g.left u') =
      (G.pullback g).s.left.fiberι u' ≫ (pullbackToTargetSquare G g).left := sorry

/-- The source fibre of a restricted groupoid is the residue-field base change of the
corresponding slicing-source fibre. -/
theorem sliceFiberMap_isPullback {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U) (u' : U'.left) :
    IsPullback (sliceFiberMap G g u')
      ((G.pullback g).s.left.fiberToSpecResidueField u')
      ((sliceSource G g).left.fiberToSpecResidueField (g.left u'))
      (Spec.map (g.left.residueFieldMap u')) := sorry

/-- The identity arrow over `u` has source `u`. -/
theorem sourceUnit_mem {S : Scheme.{u}} (G : GroupoidScheme S) (u : G.U.left) :
    G.s.left (G.e.left u) = u := sorry

/-- The identity arrow as a point of the scheme-theoretic source fibre. -/
def sourceFiberUnit {S : Scheme.{u}} (G : GroupoidScheme S) (u : G.U.left) :
    Scheme.Hom.fiber G.s.left u :=
  (Scheme.Hom.fiberHomeo G.s.left u).symm ⟨G.e.left u, sourceUnit_mem G u⟩

/-- The source-fibre identity point projects to the groupoid identity arrow. -/
theorem sourceFiberUnit_fiberι {S : Scheme.{u}} (G : GroupoidScheme S)
    (u : G.U.left) :
    Scheme.Hom.fiberι G.s.left u (sourceFiberUnit G u) = G.e.left u := sorry

/-- The stabilizer unit over `u` maps back to `u`. -/
theorem stabilizerOne_mem {S : Scheme.{u}} (G : GroupoidScheme S) (u : G.U.left) :
    (PreRelation.stabilizer G.toPreRelation).hom.left
      ((stabilizerOne G).left.left u) = u := sorry

/-- The stabilizer unit as a point of the scheme-theoretic stabilizer fibre. -/
def stabilizerFiberUnit {S : Scheme.{u}} (G : GroupoidScheme S) (u : G.U.left) :
    Scheme.Hom.fiber (PreRelation.stabilizer G.toPreRelation).hom.left u :=
  (Scheme.Hom.fiberHomeo (PreRelation.stabilizer G.toPreRelation).hom.left u).symm
    ⟨(stabilizerOne G).left.left u, stabilizerOne_mem G u⟩

/-- The stabilizer-fibre identity point projects to the unit of the stabilizer. -/
theorem stabilizerFiberUnit_fiberι {S : Scheme.{u}} (G : GroupoidScheme S)
    (u : G.U.left) :
    Scheme.Hom.fiberι (PreRelation.stabilizer G.toPreRelation).hom.left u
        (stabilizerFiberUnit G u) =
      (stabilizerOne G).left.left u := sorry

/-- The stabilizer-fibre identity point maps to the identity arrow in the arrow scheme. -/
theorem stabilizerFiberUnit_toArrows {S : Scheme.{u}} (G : GroupoidScheme S)
    (u : G.U.left) :
    (PreRelation.stabilizerToArrows G.toPreRelation).left
        (Scheme.Hom.fiberι (PreRelation.stabilizer G.toPreRelation).hom.left u
          (stabilizerFiberUnit G u)) =
      G.e.left u := sorry

/-- The restriction map sends the restricted identity arrow to the original identity arrow. -/
theorem restrictionArrow_unit {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U) (u' : U'.left) :
    (pullbackHom G g).arrow.left ((G.pullback g).e.left u') =
      G.e.left (g.left u') := sorry

/-- The square of source maps underlying the restriction morphism commutes. -/
theorem pullbackHom_source_condition {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U) :
    (pullbackHom G g).arrow.left ≫ G.s.left =
      (G.pullback g).s.left ≫ g.left := sorry

/-- The canonical map from a restricted source fibre to the original source fibre. -/
def sourceFiberMap {S : Scheme.{u}} (G : GroupoidScheme S) {U' : Over S}
    (g : U' ⟶ G.U) (u' : U'.left) :
    Scheme.Hom.fiber (G.pullback g).s.left u' ⟶
      Scheme.Hom.fiber G.s.left (g.left u') :=
  Scheme.Hom.fiberMap (G.pullback g).s.left (pullbackHom G g).arrow.left
    g.left G.s.left (CommSq.mk (pullbackHom_source_condition G g)) u'

/-- The restricted source-fibre map is compatible with the maps to the arrow schemes. -/
theorem sourceFiberMap_fiberι {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U) (u' : U'.left) :
    sourceFiberMap G g u' ≫ Scheme.Hom.fiberι G.s.left (g.left u') =
      Scheme.Hom.fiberι (G.pullback g).s.left u' ≫
        (pullbackHom G g).arrow.left := sorry

/-- The restricted source-fibre identity point maps to the original source-fibre identity
point. -/
theorem sourceFiberMap_unit {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U) (u' : U'.left) :
    sourceFiberMap G g u' (sourceFiberUnit (G.pullback g) u') =
      sourceFiberUnit G (g.left u') := sorry

/-- The canonical map from the stabilizer of a restriction to the original stabilizer. -/
def restrictionStabilizerMap {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U) :
    (PreRelation.stabilizer (G.pullback g).toPreRelation).left ⟶
      (PreRelation.stabilizer G.toPreRelation).left :=
  (pullbackHom G g).stabilizerMap

/-- The restriction stabilizer map is compatible with the maps to the arrow schemes. -/
theorem restrictionStabilizerMap_toArrows {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U) :
    restrictionStabilizerMap G g ≫ G.toPreRelation.stabilizerToArrows =
      (G.pullback g).toPreRelation.stabilizerToArrows ≫ (pullbackHom G g).arrow := sorry

/-- The restriction stabilizer map lies over `g`. -/
theorem restrictionStabilizerMap_base {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U) :
    (restrictionStabilizerMap G g).left ≫
        (PreRelation.stabilizer G.toPreRelation).hom.left =
      (PreRelation.stabilizer (G.pullback g).toPreRelation).hom.left ≫
        g.left := sorry

/-- The canonical map from a restricted stabilizer fibre to the original stabilizer fibre. -/
def stabilizerFiberMap {S : Scheme.{u}} (G : GroupoidScheme S) {U' : Over S}
    (g : U' ⟶ G.U) (u' : U'.left) :
    Scheme.Hom.fiber
        (PreRelation.stabilizer (G.pullback g).toPreRelation).hom.left u' ⟶
      Scheme.Hom.fiber (PreRelation.stabilizer G.toPreRelation).hom.left
        (g.left u') :=
  Scheme.Hom.fiberMap (PreRelation.stabilizer (G.pullback g).toPreRelation).hom.left
    (restrictionStabilizerMap G g).left g.left
    (PreRelation.stabilizer G.toPreRelation).hom.left
      (CommSq.mk (restrictionStabilizerMap_base G g)) u'

/-- The restricted stabilizer-fibre map is compatible with the maps to the stabilizer
carriers. -/
theorem stabilizerFiberMap_fiberι {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U) (u' : U'.left) :
    stabilizerFiberMap G g u' ≫
        Scheme.Hom.fiberι (PreRelation.stabilizer G.toPreRelation).hom.left
          (g.left u') =
      Scheme.Hom.fiberι
          (PreRelation.stabilizer (G.pullback g).toPreRelation).hom.left u' ≫
        (restrictionStabilizerMap G g).left := sorry

/-- The restricted stabilizer-fibre identity point maps to the original stabilizer-fibre
identity point. -/
theorem stabilizerFiberMap_unit {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U) (u' : U'.left) :
    stabilizerFiberMap G g u' (stabilizerFiberUnit (G.pullback g) u') =
      stabilizerFiberUnit G (g.left u') := sorry

end AlgebraicGeometry.GroupoidScheme
