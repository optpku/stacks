module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.Topology.Connected.Clopen
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Geometrically
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GlobalSections.OverField

/-!
# Global sections of proper algebraic spaces over a field

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

/-- If `X` is a proper algebraic space over a field `k`, then
`A = Γ(X, 𝒪_X)` is a finite-dimensional `k`-algebra. -/
instance globalSectionsFiniteDimensional [Proper (SchemeRealization.toBase X)] :
    FiniteDimensional k (globalSectionsAlg X) :=
  sorry

/-- If `X` is a proper algebraic space over a field `k`, then
`A = Γ(X, 𝒪_X)` is a product of Artinian local `k`-algebras, one factor for each
connected component of `|X|`. -/
theorem globalSectionsLocalArtinianFactorization [Proper (SchemeRealization.toBase X)] :
    ∃ (_ : Fintype (ConnectedComponents (Points X)))
      (A : ConnectedComponents (Points X) → Type u)
      (_ : ∀ i, CommRing (A i))
      (_ : ∀ i, Algebra k (A i))
      (_ : ∀ i, IsLocalRing (A i))
      (_ : globalSectionsAlg X ≃ₐ[k] ∀ i, A i),
      ∀ i, IsArtinianRing (A i) :=
  sorry

/-- If `X` is a reduced proper algebraic space over a field `k`, then
`A = Γ(X, 𝒪_X)` is a product of fields, each a finite extension of `k`, indexed by the
connected components of `|X|`. -/
theorem globalSectionsFieldFactorizationOfIsReduced [Proper (SchemeRealization.toBase X)] [IsReduced X] :
    ∃ (_ : Fintype (ConnectedComponents (Points X)))
      (K : ConnectedComponents (Points X) → Type u)
      (_ : ∀ i, Field (K i))
      (_ : ∀ i, Algebra k (K i))
      (_ : globalSectionsAlg X ≃ₐ[k] ∀ i, K i),
      ∀ i, FiniteDimensional k (K i) :=
  sorry

/-- If `X` is a geometrically reduced proper algebraic space over a
field `k`, then the field factors of `A = Γ(X, 𝒪_X)` are finite separable extensions of
`k`. -/
theorem globalSectionsSeparableFieldFactorizationOfGeometricallyReduced
    [Proper (SchemeRealization.toBase X)] [GeometricallyReduced X] :
    ∃ (_ : Fintype (ConnectedComponents (Points X)))
      (K : ConnectedComponents (Points X) → Type u)
      (_ : ∀ i, Field (K i))
      (_ : ∀ i, Algebra k (K i))
      (_ : globalSectionsAlg X ≃ₐ[k] ∀ i, K i),
      ∀ i, FiniteDimensional k (K i) ∧ Algebra.IsSeparable k (K i) :=
  sorry

/-- If `X` is a geometrically connected proper algebraic space over a
field `k`, then `A = Γ(X, 𝒪_X)` is geometrically irreducible over `k`. -/
instance globalSectionsGeometricallyIrreducibleOfGeometricallyConnected
    [Proper (SchemeRealization.toBase X)] [GeometricallyConnected X] :
    AlgebraicGeometry.GeometricallyIrreducible (globalSectionsSpecMap X) :=
  sorry

/-- If `X` is a geometrically irreducible proper algebraic space over a
field `k`, then `A = Γ(X, 𝒪_X)` is geometrically irreducible over `k`. -/
instance globalSectionsGeometricallyIrreducibleOfGeometricallyIrreducible
    [Proper (SchemeRealization.toBase X)] [GeometricallyIrreducible X] :
    AlgebraicGeometry.GeometricallyIrreducible (globalSectionsSpecMap X) :=
  sorry

/-- If `X` is a geometrically reduced and geometrically connected proper
algebraic space over a field `k`, then the canonical map `k → Γ(X, 𝒪_X)` is bijective,
so `A = k`. -/
theorem map_bijective_of_geometricallyReduced_geometricallyConnected
    [Proper (SchemeRealization.toBase X)] [GeometricallyReduced X] [GeometricallyConnected X] :
    Function.Bijective (globalSectionsMap X) :=
  sorry

/-- If `X` is a geometrically integral proper algebraic space over a
field `k`, then the canonical map `k → Γ(X, 𝒪_X)` is bijective, so `A = k`. -/
theorem globalSectionsAlgebraMapBijectiveOfGeometricallyIntegral
    [Proper (SchemeRealization.toBase X)] [GeometricallyIntegral X] :
    Function.Bijective (globalSectionsMap X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
