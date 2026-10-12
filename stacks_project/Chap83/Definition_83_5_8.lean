/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap83.Definition_83_5_8_Invariant
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

variable {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
variable (P : PreRelation U) (f : U ⟶ X)

/- Definition 83.5.8 (1): a morphism `φ : U ⟶ X` over `B` is set-theoretically `R`-invariant
when `U(k) → X(k)` equalizes `s, t : R(k) → U(k)` for every algebraically closed field `k`
over `B`. Here `U(k)` is `Over.mk kbar.hom ⟶ U`. -/
@[stacks 048V] #check
  (PreRelation.IsSetTheoreticallyInvariant P f : Prop)

/- Definition 83.5.8 (2): a morphism `φ : U ⟶ X` over `B` separates orbits, or separates
`R`-orbits, when it is set-theoretically `R`-invariant and `φ(ū) = φ(ū')` in `X(k)` implies
that `ū, ū' ∈ U(k)` lie in the same geometric `R`-orbit, for every algebraically closed
field `k` over `B`. -/
@[stacks 048V] #check
  (PreRelation.SeparatesOrbits P f : Prop)
