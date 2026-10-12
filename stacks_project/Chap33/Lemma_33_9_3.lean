/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections.Proper
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CommRingCat TopologicalSpace

universe u

/- Lemma 33.9.3 (1): for a proper scheme over a field, its global-sections algebra is
finite-dimensional over that field. -/
@[stacks 0BUG] #check (AlgebraicGeometry.globalSectionsFiniteDimensional :
  ∀ {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f],
    FiniteDimensional k (Scheme.Hom.globalSectionsAlg f))

/- Clause (2): the global-sections algebra has one local Artinian factor for each connected
component. -/
#check (AlgebraicGeometry.globalSectionsLocalArtinianFactorization :
  ∀ {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f],
    ∃ (_ : Fintype (ConnectedComponents X.carrier))
      (A : ConnectedComponents X.carrier → Type u)
      (_ : ∀ i, CommRing (A i))
      (_ : ∀ i, Algebra k (A i))
      (_ : ∀ i, IsLocalRing (A i))
      (_ : Scheme.Hom.globalSectionsAlg f ≃ₐ[k] ∀ i, A i),
      ∀ i, IsArtinianRing (A i))

/- Clause (3): reducedness makes the connected-component factors finite field extensions. -/
#check (AlgebraicGeometry.globalSectionsFieldFactorizationOfIsReduced :
  ∀ {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] [IsReduced X],
    ∃ (_ : Fintype (ConnectedComponents X.carrier))
      (K : ConnectedComponents X.carrier → Type u)
      (_ : ∀ i, Field (K i))
      (_ : ∀ i, Algebra k (K i))
      (_ : Scheme.Hom.globalSectionsAlg f ≃ₐ[k] ∀ i, K i),
      ∀ i, FiniteDimensional k (K i))

/- Clause (4): geometric reducedness makes the field factors finite separable extensions. -/
#check (AlgebraicGeometry.globalSectionsSeparableFieldFactorizationOfGeometricallyReduced :
  ∀ {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] [GeometricallyReduced f],
    ∃ (_ : Fintype (ConnectedComponents X.carrier))
      (K : ConnectedComponents X.carrier → Type u)
      (_ : ∀ i, Field (K i))
      (_ : ∀ i, Algebra k (K i))
      (_ : Scheme.Hom.globalSectionsAlg f ≃ₐ[k] ∀ i, K i),
      ∀ i, FiniteDimensional k (K i) ∧ Algebra.IsSeparable k (K i))

/- Clause (5): geometric connectedness makes the affine global-sections morphism geometrically
irreducible. -/
#check (AlgebraicGeometry.globalSectionsGeometricallyIrreducibleOfGeometricallyConnected :
  ∀ {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] [GeometricallyConnected f],
    GeometricallyIrreducible (Scheme.Hom.globalSectionsSpecMap f))

/- Clause (6): geometric irreducibility of the scheme makes the affine global-sections morphism
geometrically irreducible. -/
#check (AlgebraicGeometry.globalSectionsGeometricallyIrreducibleOfGeometricallyIrreducible :
  ∀ {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] [GeometricallyIrreducible f],
    GeometricallyIrreducible (Scheme.Hom.globalSectionsSpecMap f))

/- Clause (7): for a geometrically reduced and geometrically connected proper scheme, the
canonical map from the base field to global sections is bijective. -/
#check (AlgebraicGeometry.Scheme.GlobalSections.map_bijective_of_geometricallyReduced_geometricallyConnected :
  ∀ {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
      [GeometricallyReduced f] [GeometricallyConnected f],
    Function.Bijective (Scheme.Hom.globalSectionsMap f))

/- Clause (8): for a geometrically integral proper scheme, the canonical map from the base field
to global sections is bijective. -/
#check (AlgebraicGeometry.globalSectionsAlgebraMapBijectiveOfGeometricallyIntegral :
  ∀ {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] [GeometricallyIntegral f],
    Function.Bijective (Scheme.Hom.globalSectionsMap f))
