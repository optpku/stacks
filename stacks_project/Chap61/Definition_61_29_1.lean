/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap61.Definition_61_29_1_Derived
public import stacks_project.Chap61.Definition_61_29_1_Constructible
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProetaleDerived

/- Definition 61.29.1 (1): an object `K` of `D(X_proétale, Λ)` is constructible when it is
derived complete with respect to `I` and `K ⊗ᴸ underline{Λ / I}` has constructible cohomology
sheaves and locally has finite Tor dimension. -/
@[stacks 09C1] #check @IsConstructible

/- Definition 61.29.1 (2): `D_cons(X, Λ)` is the full subcategory of constructible objects in
`D(X_proétale, Λ)`. -/
@[stacks 09C1] #check @ProetaleConstructible
