/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.GeometricOrbit
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Lambda

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open scoped Cardinal

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PreRelation

variable {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}

/-- If both projections of a pre-relation are locally of finite type, weak equivalence of
geometric points agrees with equivalence after passage to an overfield. -/
theorem weaklyEquivalent_iff_orbitEquivalent_of_locallyOfFiniteType
    (P : PreRelation U) (k : GeometricPoint B)
    [LocallyOfFiniteType P.s.left] [LocallyOfFiniteType P.t.left]
    (x y : Over.mk k.hom ⟶ U) :
    P.weaklyEquivalent (Over.mk k.hom) x y ↔ P.orbitEquivalent k x y := sorry

/-- If both projections of a pre-relation are locally of finite type, the weak orbit of a
geometric point equals its orbit. -/
theorem weakOrbit_eq_orbit_of_locallyOfFiniteType
    (P : PreRelation U) (k : GeometricPoint B)
    [LocallyOfFiniteType P.s.left] [LocallyOfFiniteType P.t.left]
    (x : Over.mk k.hom ⟶ U) :
    P.weakOrbit (Over.mk k.hom) x = P.orbit k x := sorry

/-- If the geometric point's field has cardinality strictly greater than the cardinal bound
of a pre-relation, weak equivalence agrees with equivalence after passage to an overfield. -/
theorem weaklyEquivalent_iff_orbitEquivalent_of_lambda
    (P : PreRelation U) (k : GeometricPoint B)
    (h_lambda : lambda P.left.left < #k.K) (x y : Over.mk k.hom ⟶ U) :
    P.weaklyEquivalent (Over.mk k.hom) x y ↔ P.orbitEquivalent k x y := sorry

/-- If the geometric point's field has cardinality strictly greater than the cardinal bound
of a pre-relation, the weak orbit of the point equals its orbit. -/
theorem weakOrbit_eq_orbit_of_lambda
    (P : PreRelation U) (k : GeometricPoint B)
    (h_lambda : lambda P.left.left < #k.K) (x : Over.mk k.hom ⟶ U) :
    P.weakOrbit (Over.mk k.hom) x = P.orbit k x := sorry

end AlgebraicGeometry.AlgebraicSpace.PreRelation
