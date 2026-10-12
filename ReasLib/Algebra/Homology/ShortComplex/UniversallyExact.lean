/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import ReasLib.LinearAlgebra.UniversallyInjective

/-!
# Universally exact short complexes of modules

@stack 058I

Universal exactness combines short exactness with tensor-stable injectivity of the left map.  The
linear-map predicate itself lives in `ReasLib.LinearAlgebra.UniversallyInjective`.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace CategoryTheory.ShortComplex

variable {R : Type u} [CommRing R]
variable {S : ShortComplex (ModuleCat.{v} R)}

/-- A short complex of `R`-modules is universally exact when it is short exact and its left map
is universally injective. -/
@[stacks 058I]
def UniversallyExact (S : ShortComplex (ModuleCat.{v} R)) : Prop :=
  S.ShortExact ∧ LinearMap.UniversallyInjective.{u, v, v, max u v} S.f.hom

namespace UniversallyExact

/-- A universally exact short complex is short exact. -/
@[stacks 058I "universal exactness implies short exactness"]
theorem shortExact (hS : UniversallyExact S) :
    S.ShortExact := hS.1

/-- In a universally exact short complex, the left map is universally injective. -/
@[stacks 058I "universal exactness gives universal injectivity"]
theorem universallyInjective_f (hS : UniversallyExact S) :
    LinearMap.UniversallyInjective.{u, v, v, max u v} S.f.hom := hS.2

end UniversallyExact

end CategoryTheory.ShortComplex
