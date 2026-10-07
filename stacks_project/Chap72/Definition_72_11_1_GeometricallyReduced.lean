module

public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Reduced
public import stacks_project.Chap59.Definition_59_33_2_EtaleLocalRing
public import stacks_project.Chap66.Definition_66_22_2_EtaleLocalRing
public import stacks_project.Chap66.Lemma_66_29_5_Comparison
public import stacks_project.Chap67.Lemma_67_24_2_FieldPoints

/-!
# Geometrically reduced algebraic spaces over a field

An algebraic space `X` over a field `k` is geometrically reduced at a point `x` of `|X|`
when the étale local ring at every geometric point over `x` is geometrically reduced over
`k`. The global property is that pointwise condition at every point of `|X|`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CommRingCat
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {k : Type u} [Field k]

/-- The canonical map from a field `k` to the étale local ring of an algebraic space
over `k` at a geometric point, obtained by mapping `k` into the Zariski stalk of
`Spec k`, comparing with the scheme étale local ring, and applying the structure
morphism. -/
def etaleLocalRing.algebraMapFromField {X : AlgebraicSpace (Spec (of k))}
    (xbar : GeometricPoint X) : k →+* etaleLocalRing X xbar :=
  let xbarBase := xbar.map (toBase X)
  let s := xbarBase.toScheme
  (etaleLocalRingMap (toBase X) xbar).comp <|
    (etaleLocalRing_ofOver xbarBase).symm.toRingHom.comp <|
      (Scheme.etaleLocalRing.fromZariskiStalk (Spec (of k)) s).comp <|
        CommRingCat.Hom.hom <|
          (Scheme.ΓSpecIso (of k)).inv ≫
            (Spec (of k)).presheaf.germ ⊤ s.image trivial

/-- The étale local ring of an algebraic space over a field `k` is a `k`-algebra via
`etaleLocalRing.algebraMapFromField`. -/
instance etaleLocalRing.instAlgebra {X : AlgebraicSpace (Spec (of k))}
    (xbar : GeometricPoint X) : Algebra k (etaleLocalRing X xbar) :=
  (etaleLocalRing.algebraMapFromField xbar).toAlgebra

/-- The algebra map of `etaleLocalRing.instAlgebra` is `etaleLocalRing.algebraMapFromField`. -/
theorem etaleLocalRing.algebraMapFromField_eq {X : AlgebraicSpace (Spec (of k))}
    (xbar : GeometricPoint X) :
    algebraMap k (etaleLocalRing X xbar) = etaleLocalRing.algebraMapFromField xbar :=
  sorry

/-- An algebraic space `X` over a field `k` is geometrically reduced at a point `x`
if the étale local ring at every geometric point lying over `x` is geometrically
reduced over `k`. -/
@[mk_iff]
class GeometricallyReducedAt (X : AlgebraicSpace (Spec (of k))) (x : Points X) : Prop where
  /-- The étale local ring at every geometric point over `x` is geometrically reduced over `k`. -/
  isGeometricallyReduced_etaleLocalRing :
    ∀ xbar : GeometricPoint X, xbar.liesOver x →
      Algebra.IsGeometricallyReduced k (etaleLocalRing X xbar)

namespace GeometricallyReducedAt

/-- Geometric reducedness at `x` implies that the étale local ring at every geometric
point lying over `x` is geometrically reduced over `k`. -/
theorem spec {X : AlgebraicSpace (Spec (of k))} {x : Points X}
    [GeometricallyReducedAt X x] (xbar : GeometricPoint X) (hx : xbar.liesOver x) :
    Algebra.IsGeometricallyReduced k (etaleLocalRing X xbar) :=
  sorry

/-- The condition that every étale local ring over `x` is geometrically reduced over `k`
witnesses geometric reducedness at `x`. -/
theorem of {X : AlgebraicSpace (Spec (of k))} {x : Points X}
    (h : ∀ xbar : GeometricPoint X, xbar.liesOver x →
      Algebra.IsGeometricallyReduced k (etaleLocalRing X xbar)) :
    GeometricallyReducedAt X x :=
  sorry

end GeometricallyReducedAt

/-- `Spec k`, viewed as an algebraic space over itself, is geometrically reduced at
every point. -/
instance instGeometricallyReducedAt_ofOver_id
    (x : Points (ofOver (Over.mk (𝟙 (Spec (of k)))))) :
    GeometricallyReducedAt (ofOver (Over.mk (𝟙 (Spec (of k))))) x :=
  sorry

/-- On a scheme over `k`, viewed as an algebraic space, geometric reducedness at a point
agrees with the scheme-theoretic notion. -/
theorem geometricallyReducedAt_ofOver_iff (U : Over (Spec (of k))) (u : U.left) :
    GeometricallyReducedAt (ofOver U) (ofOver.pointsEquiv U u) ↔
      SchemeOverField.geometricallyReducedAt U u :=
  sorry

/-- An algebraic space over a field `k` is geometrically reduced if it is geometrically
reduced at every point of `|X|`. -/
@[mk_iff]
class GeometricallyReduced (X : AlgebraicSpace (Spec (of k))) : Prop where
  /-- Geometric reducedness holds at every point of `|X|`. -/
  geometricallyReducedAt : ∀ x : Points X, GeometricallyReducedAt X x

namespace GeometricallyReduced

/-- A geometrically reduced algebraic space is geometrically reduced at every point. -/
theorem spec {X : AlgebraicSpace (Spec (of k))} [GeometricallyReduced X] :
    ∀ x : Points X, GeometricallyReducedAt X x :=
  sorry

/-- The condition that `X` is geometrically reduced at every point witnesses that `X`
is geometrically reduced over `k`. -/
theorem of {X : AlgebraicSpace (Spec (of k))}
    (h : ∀ x : Points X, GeometricallyReducedAt X x) : GeometricallyReduced X :=
  sorry

end GeometricallyReduced

/-- A geometrically reduced algebraic space is geometrically reduced at each of its
points. -/
instance instGeometricallyReducedAt_of_geometricallyReduced
    {X : AlgebraicSpace (Spec (of k))} [GeometricallyReduced X] (x : Points X) :
    GeometricallyReducedAt X x :=
  sorry

/-- `Spec k`, viewed as an algebraic space over itself, is geometrically reduced over `k`. -/
instance instGeometricallyReduced_ofOver_id :
    GeometricallyReduced (ofOver (Over.mk (𝟙 (Spec (of k))))) :=
  sorry

/-- A scheme over `k`, viewed as an algebraic space, is geometrically reduced if and
only if the underlying scheme is geometrically reduced over `k`. -/
theorem geometricallyReduced_ofOver_iff (U : Over (Spec (of k))) :
    GeometricallyReduced (ofOver U) ↔ SchemeOverField.geometricallyReduced U :=
  sorry

end AlgebraicGeometry.AlgebraicSpace

