module

public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.Pullback

/-!
# Stabilizers of pre-relations

This module defines the stabilizer of a pre-relation and its canonical compatibility with
base change.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.PreRelation

/-- The stabilizer of a pre-relation is its pullback along the diagonal. -/
def stabilizer {S : Scheme.{u}} {U : Over S} (P : PreRelation U) : Over U :=
  (Over.pullback (diag U)).obj P

/-- The carrier of the stabilizer is the pullback of the relation map along the diagonal. -/
theorem stabilizer_left {S : Scheme.{u}} {U : Over S} (P : PreRelation U) :
    P.stabilizer.left = Limits.pullback P.hom (diag U) := sorry

/-- The structure map of the stabilizer is the second pullback projection. -/
theorem stabilizer_hom {S : Scheme.{u}} {U : Over S} (P : PreRelation U) :
    P.stabilizer.hom = Limits.pullback.snd P.hom (diag U) := sorry

/-- The canonical map from the stabilizer to the arrow object of the pre-relation. -/
def stabilizerToArrows {S : Scheme.{u}} {U : Over S} (P : PreRelation U) :
    P.stabilizer.left ⟶ P.left :=
  Limits.pullback.fst P.hom (diag U)

/-- The maps from the stabilizer to the arrows and to `U` form its defining pullback square. -/
theorem stabilizerToArrows_condition {S : Scheme.{u}} {U : Over S}
    (P : PreRelation U) :
    P.stabilizerToArrows ≫ P.hom = P.stabilizer.hom ≫ diag U := sorry

/-- The stabilizer of a pulled-back pre-relation is canonically the pullback of its
stabilizer. -/
def stabilizerPullbackIso {S : Scheme.{u}} {U U' : Over S} (P : PreRelation U)
    (g : U' ⟶ U) :
    (P.pullback g).stabilizer ≅ (Over.pullback g).obj P.stabilizer :=
  (Over.pullbackComp (diag U') (prod.map g g)).symm.app P ≪≫
    eqToIso (congrArg (fun h : U' ⟶ U ⨯ U ↦ (Over.pullback h).obj P)
      (prod.diag_map g)) ≪≫
    (Over.pullbackComp g (diag U)).app P

/-- The stabilizer base-change isomorphism commutes with the canonical maps to the original
arrow object. -/
theorem stabilizerPullbackIso_hom_toArrows {S : Scheme.{u}} {U U' : Over S}
    (P : PreRelation U) (g : U' ⟶ U) :
    (P.stabilizerPullbackIso g).hom.left ≫
          Limits.pullback.fst P.stabilizer.hom g ≫ P.stabilizerToArrows =
      (P.pullback g).stabilizerToArrows ≫
        Limits.pullback.fst P.hom (prod.map g g) := sorry

end AlgebraicGeometry.Scheme.PreRelation
