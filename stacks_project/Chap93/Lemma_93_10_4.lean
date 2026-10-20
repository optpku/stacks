module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap93.Lemma_93_10_3_Deformation

/-!
# Finite-dimensionality of Inf and T for proper morphisms of schemes over a field

In Lemma 93.10.3, if `X` and `Y` are both proper over `k`, then `Inf(Def_{X ⟶ Y})`
and `T Def_{X ⟶ Y}` are finite-dimensional `k`-vector spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FlatSchemeMorphismCat

universe u

namespace FlatSchemeMorphismCat

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
variable (hf : f ≫ hY = hX)
variable [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY]
variable [IsProper hX] [IsProper hY]

/-- Lemma 93.10.4 (1)
In Lemma 93.10.3, if `X` and `Y` are both proper over `k`, then `Inf(Def_{X ⟶ Y})`
is a finite-dimensional `k`-vector space. -/
@[stacks 0E3W, instance]
instance instFiniteDimensional_inf : FiniteDimensional k (inf Λ k f hX hY hf) := sorry

/-- Lemma 93.10.4 (2)
In Lemma 93.10.3, if `X` and `Y` are both proper over `k`, then `T Def_{X ⟶ Y}`
is a finite-dimensional `k`-vector space. -/
@[stacks 0E3W, instance]
instance instFiniteDimensional_tangentSpace :
    FiniteDimensional k (tangentSpace Λ k f hX hY hf) := sorry

end FlatSchemeMorphismCat
