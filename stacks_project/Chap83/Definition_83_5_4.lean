/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap83.Definition_83_5_4_Orbit
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

variable {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
variable (P : PreRelation U) (b : GeometricPoint B)
variable (x y : Over.mk b.hom ⟶ U)

/- Definition 83.5.4 (1): two `k`-points of `U` are weakly `R`-equivalent when they lie in the
same generated equivalence class of `j(R(k)) ⊆ U(k) × U(k)`, for a geometric point
`Spec(k) ⟶ B`. Here `U(k)` is `Over.mk b.hom ⟶ U`. -/
@[stacks 048Q] #check
  (PreRelation.weaklyEquivalent P (Over.mk b.hom) x y : Prop)

/- Definition 83.5.4 (2): two `k`-points of `U` are `R`-equivalent when their images in `U(Ω)`
are weakly `R`-equivalent for some overfield `k ⊂ Ω`. -/
@[stacks 048Q] #check
  (PreRelation.orbitEquivalent P b x y : Prop)

/- Definition 83.5.4 (3): the weak `R`-orbit of a `k`-point of `U` is the set of all `k`-points
weakly `R`-equivalent to it. -/
@[stacks 048Q] #check
  (PreRelation.weakOrbit P (Over.mk b.hom) x : Set (Over.mk b.hom ⟶ U))

/- Definition 83.5.4 (4): the `R`-orbit of a `k`-point of `U` is the set of all `k`-points
`R`-equivalent to it. -/
@[stacks 048Q] #check
  (PreRelation.orbit P b x : Set (Over.mk b.hom ⟶ U))
