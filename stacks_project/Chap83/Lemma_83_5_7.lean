/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.GeometricOrbit.Comparison
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open scoped Cardinal

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PreRelation

variable {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}

/- Lemma 83.5.7 (1): if `s` and `t` are locally of finite type, then weak `R`-equivalence of
geometric `k`-points of `U` agrees with `R`-equivalence. -/
@[stacks 048U]
#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.weaklyEquivalent_iff_orbitEquivalent_of_locallyOfFiniteType :
    ∀ (P : PreRelation U) (k : GeometricPoint B)
    [LocallyOfFiniteType P.s.left] [LocallyOfFiniteType P.t.left]
    (x y : Over.mk k.hom ⟶ U),
    P.weaklyEquivalent (Over.mk k.hom) x y ↔ P.orbitEquivalent k x y)

/- If `s` and `t` are locally of finite type, then the weak `R`-orbit of a geometric `k`-point
of `U` equals its `R`-orbit. -/
#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.weakOrbit_eq_orbit_of_locallyOfFiniteType :
    ∀ (P : PreRelation U) (k : GeometricPoint B)
    [LocallyOfFiniteType P.s.left] [LocallyOfFiniteType P.t.left]
    (x : Over.mk k.hom ⟶ U),
    P.weakOrbit (Over.mk k.hom) x = P.orbit k x)

/- Lemma 83.5.7 (2): if `|k| > λ(R)`, i.e. `lambda P.left.left < #k.K`, then weak
`R`-equivalence of geometric `k`-points of `U` agrees with `R`-equivalence. -/
@[stacks 048U]
#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.weaklyEquivalent_iff_orbitEquivalent_of_lambda :
    ∀ (P : PreRelation U) (k : GeometricPoint B)
    (h_lambda : lambda P.left.left < #k.K) (x y : Over.mk k.hom ⟶ U),
    P.weaklyEquivalent (Over.mk k.hom) x y ↔ P.orbitEquivalent k x y)

/- If `|k| > λ(R)`, i.e. `lambda P.left.left < #k.K`, then the weak `R`-orbit of a geometric
`k`-point of `U` equals its `R`-orbit. -/
#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.weakOrbit_eq_orbit_of_lambda :
    ∀ (P : PreRelation U) (k : GeometricPoint B)
    (h_lambda : lambda P.left.left < #k.K) (x : Over.mk k.hom ⟶ U),
    P.weakOrbit (Over.mk k.hom) x = P.orbit k x)

end AlgebraicGeometry.AlgebraicSpace.PreRelation
