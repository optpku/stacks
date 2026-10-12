/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Limits.FormalCoproduct.Objects
public import ReasLib.CategoryTheory.Sites.Family.FormalCoproduct.Adjoin
public import ReasLib.CategoryTheory.Sites.Family.FormalCoproduct.Basis
public import ReasLib.CategoryTheory.Sites.Hypercovering.FixedTarget
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pointwise properties of site hypercoverings

This leaf owns degreewise source-object and finiteness predicates for topology-relative
hypercoverings, their projection API, and the basis-valued existence theorem.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Opposite
open Limits
open SemiRepresentableFamily SemiRepresentableFamily.OverFamily
open scoped CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable {J : GrothendieckTopology C}

namespace Hypercovering

variable {X : C}

/-- A hypercovering lies degreewise in `B` when every source object in every simplicial degree
belongs to `B`. -/
@[stacks 0DAV "degreewise basis membership"]
def degreewiseObjectsIn (K : Hypercovering J X) (B : Set C) : Prop :=
  ∀ n : ℕ, FormalCoproduct.Over.objectsIn (K.family n) B

/-- Unfolding `degreewiseObjectsIn` quantifies over every simplicial degree family. -/
@[simp] theorem degreewiseObjectsIn_iff (K : Hypercovering J X) (B : Set C) :
    K.degreewiseObjectsIn B ↔
      ∀ n : ℕ, FormalCoproduct.Over.objectsIn (K.family n) B := sorry

/-- A degreewise basis-membership condition supplies the condition for any chosen degree. -/
theorem degreewiseObjectsIn.family
    {K : Hypercovering J X} {B : Set C} (hK : K.degreewiseObjectsIn B) (n : ℕ) :
    FormalCoproduct.Over.objectsIn (K.family n) B := sorry

/-- Every source object in a chosen degree of a degreewise basis hypercovering belongs to the
chosen basis. -/
theorem degreewiseObjectsIn.mem
    {K : Hypercovering J X} {B : Set C} (hK : K.degreewiseObjectsIn B)
    (n : ℕ) (i : (K.family n).index) :
    ((K.family n).obj i).left ∈ B := sorry

/-- Degreewise object membership is monotone in the collection of allowed objects. -/
theorem degreewiseObjectsIn.mono
    {K : Hypercovering J X} {B B' : Set C} (hK : K.degreewiseObjectsIn B)
    (hBB' : B ⊆ B') :
    K.degreewiseObjectsIn B' := sorry

/-- A hypercovering is degreewise finite when each simplicial degree family has finite index
type. -/
@[stacks 094K "degreewise finite index condition"]
def degreewiseFinite (K : Hypercovering J X) : Prop :=
  ∀ n : ℕ, Finite ((K.family n).index)

/-- Unfolding `degreewiseFinite` quantifies over all simplicial degree-family index types. -/
@[simp] theorem degreewiseFinite_iff (K : Hypercovering J X) :
    K.degreewiseFinite ↔ ∀ n : ℕ, Finite ((K.family n).index) := sorry

/-- A degreewise finite hypercovering has finite index type in any chosen degree. -/
theorem degreewiseFinite.finite
    {K : Hypercovering J X} (hK : K.degreewiseFinite) (n : ℕ) :
    Finite ((K.family n).index) := sorry

/-- A degreewise finite hypercovering has finite degree-zero index type. -/
theorem degreewiseFinite.zero
    {K : Hypercovering J X} (hK : K.degreewiseFinite) :
    Finite ((K.family 0).index) := sorry

/-- A degreewise finite hypercovering has finite degree-one index type. -/
theorem degreewiseFinite.one
    {K : Hypercovering J X} (hK : K.degreewiseFinite) :
    Finite ((K.family 1).index) := sorry

/-- A degreewise finite hypercovering has finite index type in every successor degree. -/
theorem degreewiseFinite.succ
    {K : Hypercovering J X} (hK : K.degreewiseFinite) (n : ℕ) :
    Finite ((K.family (n + 1)).index) := sorry

/-- Every degree family of a hypercovering is a covering family of its fixed target. -/
@[stacks 0DEQ "every hypercovering degree is covering"]
theorem family_isCovering (K : Hypercovering J X) (n : ℕ) :
    (K.family n).toSieve ∈ J X := sorry

/-- Every face map of a hypercovering is a covering morphism of fixed-target families. -/
@[stacks 0DEQ "hypercovering face maps are covering"]
theorem faceMap_isCovering
    (K : Hypercovering J X) (n : ℕ) (i : Fin (n + 2)) :
    SemiRepresentableFamily.OverFamily.covering J (K.toSimplicialObject.δ i) := sorry

/-- Lemma 25.12.2 (0DAV): if every object has a covering family with sources in `B`, and adjoining
one arrow from an object of `B` preserves covering, then every object has a hypercovering whose
sources lie degreewise in `B`. -/
@[stacks 0DAV "basis-valued fixed-target hypercovering"]
theorem exists_degreewiseObjectsIn
    (B : Set C)
    (hcover : ∀ U : C, ∃ 𝒰 : OverFamily.{v, u, w} U,
      𝒰.IsBasisCovering J.toPrecoverage B)
    (hadd : ∀ {U : C} (𝒰 : OverFamily.{v, u, w} U)
      (h𝒰 : 𝒰.IsBasisCovering J.toPrecoverage B)
      {U' : C} (f : U' ⟶ U) (hU' : U' ∈ B), (𝒰.addSingleton f).toSieve ∈ J U)
    (X : C) :
    ∃ K : Hypercovering.{w} J X, K.degreewiseObjectsIn B := sorry

end Hypercovering

end CategoryTheory
