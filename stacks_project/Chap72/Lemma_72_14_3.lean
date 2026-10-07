module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.Topology.Connected.Clopen
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Lemma_67_24_2_FieldPoints
public import stacks_project.Chap72.Lemma_72_14_3_Geometrically
public import stacks_project.Chap72.Lemma_72_14_3_GlobalSections

/-!
# Lemma 72.14.3

Global sections of a proper algebraic space over a field form a finite-dimensional
algebra, with Artinian, reduced, separable, and geometric factorizations indexed by
the connected components of `|X|`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory CommRingCat
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {k : Type u} [Field k] {X : AlgebraicSpace (Spec (of k))}

/-- Lemma 72.14.3 (1): if `X` is a proper algebraic space over a field `k`, then
`A = Γ(X, 𝒪_X)` is a finite-dimensional `k`-algebra. -/
@[stacks 0DMY]
instance globalSectionsFiniteDimensional [Proper (toBase X)] :
    FiniteDimensional k (globalSectionsAlg X) :=
  sorry

/-- Lemma 72.14.3 (2): if `X` is a proper algebraic space over a field `k`, then
`A = Γ(X, 𝒪_X)` is a product of Artinian local `k`-algebras, one factor for each
connected component of `|X|`. -/
@[stacks 0DMY]
theorem globalSectionsLocalArtinianFactorization [Proper (toBase X)] :
    ∃ (_ : Fintype (ConnectedComponents (Points X)))
      (A : ConnectedComponents (Points X) → Type u)
      (_ : ∀ i, CommRing (A i))
      (_ : ∀ i, Algebra k (A i))
      (_ : ∀ i, IsLocalRing (A i))
      (_ : globalSectionsAlg X ≃ₐ[k] ∀ i, A i),
      ∀ i, IsArtinianRing (A i) :=
  sorry

/-- Lemma 72.14.3 (3): if `X` is a reduced proper algebraic space over a field `k`, then
`A = Γ(X, 𝒪_X)` is a product of fields, each a finite extension of `k`, indexed by the
connected components of `|X|`. -/
@[stacks 0DMY]
theorem globalSectionsFieldFactorizationOfIsReduced [Proper (toBase X)] [IsReduced X] :
    ∃ (_ : Fintype (ConnectedComponents (Points X)))
      (K : ConnectedComponents (Points X) → Type u)
      (_ : ∀ i, Field (K i))
      (_ : ∀ i, Algebra k (K i))
      (_ : globalSectionsAlg X ≃ₐ[k] ∀ i, K i),
      ∀ i, FiniteDimensional k (K i) :=
  sorry

/-- Lemma 72.14.3 (4): if `X` is a geometrically reduced proper algebraic space over a
field `k`, then the field factors of `A = Γ(X, 𝒪_X)` are finite separable extensions of
`k`. -/
@[stacks 0DMY]
theorem globalSectionsSeparableFieldFactorizationOfGeometricallyReduced
    [Proper (toBase X)] [GeometricallyReduced X] :
    ∃ (_ : Fintype (ConnectedComponents (Points X)))
      (K : ConnectedComponents (Points X) → Type u)
      (_ : ∀ i, Field (K i))
      (_ : ∀ i, Algebra k (K i))
      (_ : globalSectionsAlg X ≃ₐ[k] ∀ i, K i),
      ∀ i, FiniteDimensional k (K i) ∧ Algebra.IsSeparable k (K i) :=
  sorry

/-- Lemma 72.14.3 (5): if `X` is a geometrically connected proper algebraic space over a
field `k`, then `A = Γ(X, 𝒪_X)` is geometrically irreducible over `k`. -/
@[stacks 0DMY]
instance globalSectionsGeometricallyIrreducibleOfGeometricallyConnected
    [Proper (toBase X)] [GeometricallyConnected X] :
    AlgebraicGeometry.GeometricallyIrreducible (globalSectionsSpecMap X) :=
  sorry

/-- Lemma 72.14.3 (6): if `X` is a geometrically irreducible proper algebraic space over a
field `k`, then `A = Γ(X, 𝒪_X)` is geometrically irreducible over `k`. -/
@[stacks 0DMY]
instance globalSectionsGeometricallyIrreducibleOfGeometricallyIrreducible
    [Proper (toBase X)] [GeometricallyIrreducible X] :
    AlgebraicGeometry.GeometricallyIrreducible (globalSectionsSpecMap X) :=
  sorry

/-- Lemma 72.14.3 (7): if `X` is a geometrically reduced and geometrically connected proper
algebraic space over a field `k`, then the canonical map `k → Γ(X, 𝒪_X)` is bijective,
so `A = k`. -/
@[stacks 0DMY]
theorem map_bijective_of_geometricallyReduced_geometricallyConnected
    [Proper (toBase X)] [GeometricallyReduced X] [GeometricallyConnected X] :
    Function.Bijective (globalSectionsMap X) :=
  sorry

/-- Lemma 72.14.3 (8): if `X` is a geometrically integral proper algebraic space over a
field `k`, then the canonical map `k → Γ(X, 𝒪_X)` is bijective, so `A = k`. -/
@[stacks 0DMY]
theorem globalSectionsAlgebraMapBijectiveOfGeometricallyIntegral
    [Proper (toBase X)] [GeometricallyIntegral X] :
    Function.Bijective (globalSectionsMap X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
