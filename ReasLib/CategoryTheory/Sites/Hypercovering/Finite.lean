/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.Finite.Sum
public import ReasLib.CategoryTheory.Sites.Family.FormalCoproduct.Adjoin
public import ReasLib.CategoryTheory.Sites.Family.FormalCoproduct.Basis
public import ReasLib.CategoryTheory.Sites.Hypercovering.Properties

/-!
# Finite basis coverings and hypercoverings

This leaf combines the independent basis-covering and finite-index conditions on a fixed-target
formal coproduct family. It provides the closure calculation for adjoining one basis arrow and
the existence theorem for degreewise finite basis-valued hypercoverings.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Limits
open SemiRepresentableFamily
open scoped CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

namespace Limits
namespace FormalCoproduct

variable {U : C}

/-- A fixed-target formal coproduct over `X` is a finite `B`-basis covering family when it is a
basis covering family for `J.toPrecoverage` and has finite index type. -/
@[stacks 094K "finite basis covering family"]
def IsFiniteBasisCovering
    (J : GrothendieckTopology C) (B : Set C)
    (𝒰 : FormalCoproduct.{w} (CategoryTheory.Over U)) : Prop :=
  𝒰.IsBasisCovering J.toPrecoverage B ∧ Finite 𝒰.index

/-- Unfolding `IsFiniteBasisCovering` gives its basis-covering and finite-index components. -/
@[simp] theorem isFiniteBasisCovering_iff
    (J : GrothendieckTopology C) (B : Set C)
    (𝒰 : FormalCoproduct.{w} (CategoryTheory.Over U)) :
    𝒰.IsFiniteBasisCovering J B ↔ 𝒰.IsBasisCovering J.toPrecoverage B ∧ Finite 𝒰.index := sorry

/-- For a Grothendieck topology, a finite basis covering family is exactly a family whose
generated sieve is covering, whose source objects lie in the basis, and whose index is finite. -/
@[simp] theorem isFiniteBasisCovering_toPrecoverage_iff
    (J : GrothendieckTopology C) (B : Set C)
    (𝒰 : FormalCoproduct.{w} (CategoryTheory.Over U)) :
    𝒰.IsFiniteBasisCovering J B ↔
      𝒰.toSieve ∈ J U ∧ FormalCoproduct.Over.objectsIn 𝒰 B ∧ Finite 𝒰.index := sorry

/-- A finite basis covering family is a basis covering family. -/
theorem IsFiniteBasisCovering.isBasisCovering
    {J : GrothendieckTopology C} {B : Set C}
    {𝒰 : FormalCoproduct.{w} (CategoryTheory.Over U)}
    (h𝒰 : 𝒰.IsFiniteBasisCovering J B) :
    𝒰.IsBasisCovering J.toPrecoverage B := sorry

/-- Every source object of a finite basis covering family belongs to the chosen basis. -/
theorem IsFiniteBasisCovering.mem_basis
    {J : GrothendieckTopology C} {B : Set C}
    {𝒰 : FormalCoproduct.{w} (CategoryTheory.Over U)}
    (h𝒰 : 𝒰.IsFiniteBasisCovering J B) (i : 𝒰.index) :
    (𝒰.obj i).left ∈ B := sorry

/-- A finite basis covering family lies in its designated basis. -/
theorem IsFiniteBasisCovering.objectsIn
    {J : GrothendieckTopology C} {B : Set C}
    {𝒰 : FormalCoproduct.{w} (CategoryTheory.Over U)}
    (h𝒰 : 𝒰.IsFiniteBasisCovering J B) :
    FormalCoproduct.Over.objectsIn 𝒰 B := sorry

/-- The generated sieve of a finite basis covering family is covering. -/
theorem IsFiniteBasisCovering.toSieve_mem
    {J : GrothendieckTopology C} {B : Set C}
    {𝒰 : FormalCoproduct.{w} (CategoryTheory.Over U)}
    (h𝒰 : 𝒰.IsFiniteBasisCovering J B) :
    𝒰.toSieve ∈ J U := sorry

/-- A finite basis covering family has finite index type. -/
theorem IsFiniteBasisCovering.finiteIndex
    {J : GrothendieckTopology C} {B : Set C}
    {𝒰 : FormalCoproduct.{w} (CategoryTheory.Over U)}
    (h𝒰 : 𝒰.IsFiniteBasisCovering J B) :
    Finite 𝒰.index := sorry

/-- Adjoining one arrow from an object of `B` to a finite basis covering family again yields a
finite basis covering family when the enlarged generated sieve is covering. -/
theorem IsFiniteBasisCovering.addSingleton
    {J : GrothendieckTopology C} {B : Set C}
    {𝒰 : FormalCoproduct.{w} (CategoryTheory.Over U)}
    (h𝒰 : 𝒰.IsFiniteBasisCovering J B)
    {U' : C} (f : U' ⟶ U) (hU' : U' ∈ B)
    (hcover : (𝒰.addSingleton f).toSieve ∈ J U) :
    (𝒰.addSingleton f).IsFiniteBasisCovering J B := sorry

end FormalCoproduct
end Limits

open SemiRepresentableFamily.OverFamily

namespace Hypercovering

variable [HasPullbacks C]

/-- Lemma 25.12.6 (094K): if every object has a finite covering family with sources in `B`, and
adjoining one arrow from an object of `B` to such a family preserves covering, then every object
has a hypercovering whose degree families have finite indices and sources in `B`. -/
@[stacks 094K "finite basis-valued fixed-target hypercovering"]
theorem exists_degreewiseFiniteIn
    (B : Set C)
    (hcover : ∀ U : C, ∃ 𝒰 : OverFamily.{v, u, w} U, 𝒰.IsFiniteBasisCovering J B)
    (hadd : ∀ {U : C} (𝒰 : OverFamily.{v, u, w} U)
      (h𝒰 : 𝒰.IsFiniteBasisCovering J B)
      {U' : C} (f : U' ⟶ U) (hU' : U' ∈ B), (𝒰.addSingleton f).toSieve ∈ J U)
    (X : C) :
    ∃ K : Hypercovering.{w} J X, K.degreewiseObjectsIn B ∧ K.degreewiseFinite := sorry

end Hypercovering

end CategoryTheory
