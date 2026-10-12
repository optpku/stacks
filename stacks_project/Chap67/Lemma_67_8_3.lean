/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Spectral.Hom
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap67.Lemma_67_53_4_UniversalHomeomorphism

/-!
# Quasi-compact morphisms induce quasi-compact maps on points

A quasi-compact morphism of algebraic spaces induces a quasi-compact map of
underlying point spaces: inverse images of quasi-compact opens are quasi-compact.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The map on points induced by `f` is spectral with respect to the given
topologies on the source and target point spaces. -/
def isSpectralMapOnPoints {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (τX : TopologicalSpace (Points X)) (τY : TopologicalSpace (Points Y))
    (f : X ⟶ Y) : Prop :=
  @IsSpectralMap (Points X) (Points Y) τX τY (Points.map f)

/-- Being a spectral map on points means the induced map is continuous and
sends compact opens in the target to compact preimages in the source. -/
theorem isSpectralMapOnPoints_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (τX : TopologicalSpace (Points X)) (τY : TopologicalSpace (Points Y))
    (f : X ⟶ Y) :
    isSpectralMapOnPoints τX τY f ↔
      @Continuous (Points X) (Points Y) τX τY (Points.map f) ∧
        ∀ (V : Set (Points Y)),
          @IsOpen (Points Y) τY V → @IsCompact (Points Y) τY V →
            @IsCompact (Points X) τX (Points.map f ⁻¹' V) :=
  sorry

namespace QuasiCompact

/-- Lemma 67.8.3: Let `S` be a scheme. If `f : X ⟶ Y` is a quasi-compact morphism
of algebraic spaces over `S`, then the underlying map `|f| : |X| ⟶ |Y|` of
topological spaces is quasi-compact. -/
@[stacks 0EMK]
theorem isSpectralMap {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] {τX : TopologicalSpace (Points X)}
    {τY : TopologicalSpace (Points Y)} (hX : IsPointsTopology X τX)
    (hY : IsPointsTopology Y τY) : isSpectralMapOnPoints τX τY f :=
  sorry

/-- The inverse image of a quasi-compact open in the target point space under a
quasi-compact morphism of algebraic spaces is quasi-compact. -/
theorem isCompact_preimage {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] {τX : TopologicalSpace (Points X)}
    {τY : TopologicalSpace (Points Y)} (hX : IsPointsTopology X τX)
    (hY : IsPointsTopology Y τY) {V : Set (Points Y)}
    (hV : @IsOpen (Points Y) τY V) (hVc : @IsCompact (Points Y) τY V) :
    @IsCompact (Points X) τX (Points.map f ⁻¹' V) :=
  sorry

end QuasiCompact

end AlgebraicGeometry.AlgebraicSpace
