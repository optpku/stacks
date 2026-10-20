/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Sober
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension.LocalRing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversalHomeomorphism

/-!
# DVR-or-field valuative squares of algebraic spaces

A finite-type morphism of algebraic spaces over a locally Noetherian target admits valuative
squares whose valuation ring is a discrete valuation ring, except that a trivial specialization
naturally produces a field. The generic field is realized as the residue field of a generic point
on a scheme étale over the source.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A valuative square over a morphism of algebraic spaces whose generic map is the residue-field
map of a generic point of an étale scheme chart and whose valuation subring is either a discrete
valuation ring or a field. -/
structure DvrOrFieldValuativeCommSqAt {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) where
  /-- The source scheme of the étale chart. -/
  U : Over S
  /-- The étale chart morphism `ofOver U ⟶ X`. -/
  toSource : ofOver U ⟶ X
  /-- The chart morphism is étale. -/
  toSource_etale : Etale toSource
  /-- The generic point of the étale chart determining the residue field `K`. -/
  sourcePoint : U.left
  /-- The source point is generic in an irreducible component of the étale chart. -/
  sourcePoint_mem : sourcePoint ∈ genericPoints U.left
  /-- The valuation subring of the residue field of the source point. -/
  V : ValuationSubring (U.left.residueField sourcePoint)
  /-- The valuation subring is a discrete valuation ring or is the whole generic field. -/
  dvrOrField : IsDiscreteValuationRing V ∨ IsField V
  /-- The structure morphism of `Spec(A)` over `S`. -/
  structureHom : Spec (.of V) ⟶ S
  /-- The residue-field map of the chart is compatible with the structure morphism of `Spec(A)`. -/
  structureHom_fac :
    U.left.fromSpecResidueField sourcePoint ≫ U.hom =
      Spec.map (CommRingCat.ofHom (algebraMap V (U.left.residueField sourcePoint))) ≫
        structureHom
  /-- The map from `Spec(A)` to the target algebraic space. -/
  toTarget : ofOver (Over.mk structureHom) ⟶ Y
  /-- The generic residue-field map and the valuation-spectrum map form a commutative square. -/
  commSq :
    CommSq
      (ofOverHomMk (U.left.fromSpecResidueField sourcePoint) structureHom_fac ≫ toSource)
      (ofOverHomMk
        (Spec.map (CommRingCat.ofHom (algebraMap V (U.left.residueField sourcePoint)))) rfl)
      f toTarget

namespace DvrOrFieldValuativeCommSqAt

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}

/-- Assemble a DVR-or-field valuative square from an étale chart, a generic residue field, a
valuation subring, and the two solid arrows over `S`. -/
def of (U : Over S) (toSource : ofOver U ⟶ X) (toSource_etale : Etale toSource)
    (sourcePoint : U.left) (sourcePoint_mem : sourcePoint ∈ genericPoints U.left)
    (V : ValuationSubring (U.left.residueField sourcePoint))
    (dvrOrField : IsDiscreteValuationRing V ∨ IsField V)
    (structureHom : Spec (.of V) ⟶ S)
    (structureHom_fac :
      U.left.fromSpecResidueField sourcePoint ≫ U.hom =
        Spec.map (CommRingCat.ofHom (algebraMap V (U.left.residueField sourcePoint))) ≫
          structureHom)
    (toTarget : ofOver (Over.mk structureHom) ⟶ Y)
    (commSq :
      CommSq
        (ofOverHomMk (U.left.fromSpecResidueField sourcePoint) structureHom_fac ≫ toSource)
        (ofOverHomMk
          (Spec.map (CommRingCat.ofHom (algebraMap V (U.left.residueField sourcePoint)))) rfl)
        f toTarget) :
    DvrOrFieldValuativeCommSqAt f where
  U := U
  toSource := toSource
  toSource_etale := toSource_etale
  sourcePoint := sourcePoint
  sourcePoint_mem := sourcePoint_mem
  V := V
  dvrOrField := dvrOrField
  structureHom := structureHom
  structureHom_fac := structureHom_fac
  toTarget := toTarget
  commSq := commSq

/-- The canonical map `Spec(K) ⟶ X` of a DVR-or-field valuative square. -/
abbrev genericToSource (sq : DvrOrFieldValuativeCommSqAt f) :
    ofOver
      (Over.mk
        (Spec.map
            (CommRingCat.ofHom
              (algebraMap sq.V (sq.U.left.residueField sq.sourcePoint))) ≫
          sq.structureHom)) ⟶
      X :=
  ofOverHomMk (sq.U.left.fromSpecResidueField sq.sourcePoint) sq.structureHom_fac ≫ sq.toSource

/-- The vertical map `Spec(K) ⟶ Spec(A)` of a DVR-or-field valuative square. -/
abbrev verticalMap (sq : DvrOrFieldValuativeCommSqAt f) :
    ofOver
      (Over.mk
        (Spec.map
            (CommRingCat.ofHom
              (algebraMap sq.V (sq.U.left.residueField sq.sourcePoint))) ≫
          sq.structureHom)) ⟶
      ofOver (Over.mk sq.structureHom) :=
  ofOverHomMk
    (Spec.map (CommRingCat.ofHom (algebraMap sq.V (sq.U.left.residueField sq.sourcePoint)))) rfl

/-- Forget the distinguished étale chart and the DVR-or-field alternative, retaining the
underlying valuative square of algebraic spaces. -/
noncomputable def toValuativeCommSq (sq : DvrOrFieldValuativeCommSqAt f) : ValuativeCommSq f :=
  ValuativeCommSq.of sq.V (sq.U.left.residueField sq.sourcePoint) sq.structureHom
    sq.genericToSource sq.toTarget sq.commSq

/-- The image in `|Y|` of the closed point of `Spec(A)`. -/
noncomputable def closedPointImage (sq : DvrOrFieldValuativeCommSqAt f) : Points Y :=
  Points.mapOfOver sq.toTarget (IsLocalRing.closedPoint sq.V)

/-- The point `x ∈ |X|` corresponding to `Spec(K) ⟶ X`. -/
noncomputable def sourceSpacePoint (sq : DvrOrFieldValuativeCommSqAt f) : Points X :=
  Points.mapOfOver sq.toSource sq.sourcePoint

/-- A DVR-or-field valuative square records étaleness of the chart, generic-point membership, the
DVR-or-field alternative, compatibility of structure morphisms, and commutativity of the solid
square. -/
theorem spec (sq : DvrOrFieldValuativeCommSqAt f) :
    Etale sq.toSource ∧
      sq.sourcePoint ∈ genericPoints sq.U.left ∧
      (IsDiscreteValuationRing sq.V ∨ IsField sq.V) ∧
      (sq.U.left.fromSpecResidueField sq.sourcePoint ≫ sq.U.hom =
        Spec.map
            (CommRingCat.ofHom
              (algebraMap sq.V (sq.U.left.residueField sq.sourcePoint))) ≫
          sq.structureHom) ∧
      sq.genericToSource ≫ f = sq.verticalMap ≫ sq.toTarget :=
  sorry

/-- The source point of `Spec(K) ⟶ X` has local-ring dimension `0`. -/
theorem localRingDimAt_sourceSpacePoint (sq : DvrOrFieldValuativeCommSqAt f) :
    localRingDimAt sq.sourceSpacePoint = 0 :=
  sorry

end DvrOrFieldValuativeCommSqAt

/-- If `f : X ⟶ Y` is a finite-type morphism of algebraic spaces over a scheme
`S` and `Y` is locally Noetherian, then every point `y` of `|Y|` in the closure of the image of
`|f|` is the image of the closed point of `Spec(A)` in a commutative valuative square
`Spec(K) ⟶ X` over `Spec(A) ⟶ Y`, where `A` is a discrete valuation ring or a field and
`K` is its field of fractions. The source point of `Spec(K) ⟶ X` may be taken of étale-local
codimension `0`, with `K` the residue field of a point of a scheme étale over `X`. -/
@[stacks 0CMC]
theorem exists_dvrOrFieldValuativeCommSqAt_of_mem_closure_range
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [FiniteType f] [IsLocallyNoetherian Y]
    {y : Points Y} {τ : TopologicalSpace (Points Y)}
    (hτ : IsPointsTopology Y τ)
    (hy : y ∈ @closure (Points Y) τ (Set.range (Points.map f))) :
    ∃ sq : DvrOrFieldValuativeCommSqAt f, sq.closedPointImage = y :=
  sorry


end AlgebraicGeometry.AlgebraicSpace
