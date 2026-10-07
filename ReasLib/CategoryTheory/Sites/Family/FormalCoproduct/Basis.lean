module

public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import ReasLib.CategoryTheory.Limits.FormalCoproduct.Objects
public import ReasLib.CategoryTheory.Sites.Family.FormalCoproduct
public import ReasLib.CategoryTheory.Sites.Family.FormalCoproduct.Adjoin
import Mathlib.Tactic.CrossRefAttribute

/-!
# Basis conditions on fixed-target formal coproducts

This leaf owns precoverage and Grothendieck-topology covering conditions for fixed-target formal
coproducts, together with their conjunction with object-membership conditions.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open SemiRepresentableFamily.OverFamily

namespace Limits
namespace FormalCoproduct

variable {C : Type u} [Category.{v} C] {U : C}

/-- A fixed-target formal coproduct is covering for a precoverage when its generated presieve
belongs to that precoverage. -/
abbrev IsCovering (K : Precoverage C) (𝒰 : FormalCoproduct.{w} (CategoryTheory.Over U)) : Prop :=
  𝒰.toPresieve ∈ K U

/-- For the precoverage associated to a Grothendieck topology, the formal-coproduct covering
condition is exactly membership of the generated sieve in that topology. -/
@[simp] theorem isCovering_toPrecoverage_iff
    (J : GrothendieckTopology C) (𝒰 : FormalCoproduct.{w} (CategoryTheory.Over U)) :
    IsCovering J.toPrecoverage 𝒰 ↔ 𝒰.toSieve ∈ J U := sorry

/-- Equation 25.12.2.1 (0DAW): a fixed-target formal coproduct is a basis covering family when it
covers for the specified precoverage and all of its source objects lie in the chosen basis. -/
@[stacks 0DAW "basis covering family"]
def IsBasisCovering
    (K : Precoverage C) (B : Set C) (𝒰 : FormalCoproduct.{w} (CategoryTheory.Over U)) : Prop :=
  IsCovering K 𝒰 ∧ FormalCoproduct.Over.objectsIn 𝒰 B

/-- Unfolding `IsBasisCovering` gives its covering and source-membership components. -/
@[simp] theorem isBasisCovering_iff
    (K : Precoverage C) (B : Set C) (𝒰 : FormalCoproduct.{w} (CategoryTheory.Over U)) :
    𝒰.IsBasisCovering K B ↔
      IsCovering K 𝒰 ∧ FormalCoproduct.Over.objectsIn 𝒰 B := sorry

/-- For a Grothendieck topology, a basis covering family is exactly a family whose generated
sieve is covering and whose source objects lie in the designated basis. -/
@[simp] theorem isBasisCovering_toPrecoverage_iff
    (J : GrothendieckTopology C) (B : Set C) (𝒰 : FormalCoproduct.{w} (CategoryTheory.Over U)) :
    𝒰.IsBasisCovering J.toPrecoverage B ↔
      𝒰.toSieve ∈ J U ∧ FormalCoproduct.Over.objectsIn 𝒰 B := sorry

/-- A basis covering family is covering for its underlying precoverage. -/
theorem IsBasisCovering.isCovering
    {K : Precoverage C} {B : Set C} {𝒰 : FormalCoproduct.{w} (CategoryTheory.Over U)}
    (h𝒰 : 𝒰.IsBasisCovering K B) :
    IsCovering K 𝒰 := sorry

/-- Every source object of a basis covering family belongs to the designated basis. -/
theorem IsBasisCovering.mem_basis
    {K : Precoverage C} {B : Set C} {𝒰 : FormalCoproduct.{w} (CategoryTheory.Over U)}
    (h𝒰 : 𝒰.IsBasisCovering K B) (i : 𝒰.I) :
    (𝒰.obj i).left ∈ B := sorry

/-- A basis covering family lies in its designated basis. -/
theorem IsBasisCovering.objectsIn
    {K : Precoverage C} {B : Set C} {𝒰 : FormalCoproduct.{w} (CategoryTheory.Over U)}
    (h𝒰 : 𝒰.IsBasisCovering K B) :
    FormalCoproduct.Over.objectsIn 𝒰 B := sorry

/-- Adjoining one arrow gives a basis covering exactly when the enlarged family covers, the old
sources lie in the basis, and the new source lies in the basis. -/
@[simp] theorem addSingleton_isBasisCovering_iff
    (K : Precoverage C) (B : Set C) (𝒰 : FormalCoproduct.{w} (CategoryTheory.Over U))
    {U' : C} (f : U' ⟶ U) :
    (𝒰.addSingleton f).IsBasisCovering K B ↔
      IsCovering K (𝒰.addSingleton f) ∧
        FormalCoproduct.Over.objectsIn 𝒰 B ∧ U' ∈ B := sorry

/-- A basis covering remains a basis covering after adjoining an arrow whose source lies in the
basis, provided that the enlarged family covers. -/
@[stacks 0DAV "basis covering after adjoining one arrow"]
theorem IsBasisCovering.addSingleton
    {K : Precoverage C} {B : Set C} {𝒰 : FormalCoproduct.{w} (CategoryTheory.Over U)}
    (h𝒰 : 𝒰.IsBasisCovering K B) {U' : C} (f : U' ⟶ U) (hU' : U' ∈ B)
    (hcover : IsCovering K (𝒰.addSingleton f)) :
    (𝒰.addSingleton f).IsBasisCovering K B := sorry

/-- The indexed-arrow presentation of a basis covering family is its precoverage covering
condition together with pointwise membership of the supplied source objects. -/
@[simp] theorem ofArrows_isBasisCovering_iff
    (K : Precoverage C) (B : Set C) {I : Type w} (X : I → C) (f : ∀ i : I, X i ⟶ U) :
    (ofArrows X f).IsBasisCovering K B ↔
      IsCovering K (ofArrows X f) ∧ ∀ i : I, X i ∈ B := sorry

/-- The indexed-arrow presentation of a Grothendieck-topology basis covering family is its
generated covering sieve together with pointwise source membership. -/
@[simp] theorem ofArrows_isBasisCovering_toPrecoverage_iff
    (J : GrothendieckTopology C) (B : Set C) {I : Type w} (X : I → C)
    (f : ∀ i : I, X i ⟶ U) :
    (ofArrows X f).IsBasisCovering J.toPrecoverage B ↔
      Sieve.ofArrows X f ∈ J U ∧ ∀ i : I, X i ∈ B := sorry

end FormalCoproduct
end Limits

end CategoryTheory
