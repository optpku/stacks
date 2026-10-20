module

public import ReasLib.CategoryTheory.Limits.FormalCoproduct.Equivalence
public import Mathlib.CategoryTheory.Comma.Over.Basic
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe w₂ w₁ v u

variable {C : Type u} [Category.{v} C] {U : C}

/- Definition 7.8.2 (1): two families of morphisms with fixed target 𝒰 and 𝒱
are combinatorially equivalent if there exist reindexings
α : 𝒰.I → 𝒱.I and β : 𝒱.I → 𝒰.I such that the displayed
arrows in Over U agree, i.e. 𝒰.obj i = 𝒱.obj (α i) and 𝒱.obj j = 𝒰.obj (β j). -/
@[stacks 00VU] #check
  (CategoryTheory.Limits.FormalCoproduct.CombinatoriallyEquivalent :
    FormalCoproduct.{w₁} (CategoryTheory.Over U) →
      FormalCoproduct.{w₂} (CategoryTheory.Over U) → Prop)

/- Definition 7.8.2 (2): two families of morphisms with fixed target 𝒰 and 𝒱
are tautologically equivalent if there exist reindexings both ways with
component isomorphisms in the slice Over U, equivalently commuting
triangles over U with isomorphisms as horizontal arrows. -/
@[stacks 00VU] #check
  (CategoryTheory.Limits.FormalCoproduct.TautologicallyEquivalent :
    FormalCoproduct.{w₁} (CategoryTheory.Over U) →
      FormalCoproduct.{w₂} (CategoryTheory.Over U) → Prop)
