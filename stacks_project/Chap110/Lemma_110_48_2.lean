/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.GroupScheme
public import ReasLib.AlgebraicGeometry.GroupScheme.Properties
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.GroupScheme

/-- Lemma 110.48.2: there exists a group scheme over infinite-dimensional affine
space which is flat and of finite type, but not quasi-separated. -/
@[stacks 08IX]
theorem exists_flat_finiteType_not_quasiSeparated_over_infiniteAffineSpace
    {k : Type u} [Field k] :
    ∃ G : GroupScheme (𝔸(ULift.{u} ℕ; Spec (CommRingCat.of k))),
      AlgebraicGeometry.Flat G.X.hom ∧ Scheme.Hom.FiniteType G.X.hom ∧
        ¬ AlgebraicGeometry.QuasiSeparated G.X.hom := sorry

end AlgebraicGeometry.GroupScheme
