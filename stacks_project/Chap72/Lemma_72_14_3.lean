module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GlobalSections.Proper

@[expose] public section

open CategoryTheory AlgebraicGeometry CommRingCat
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 72.14.3: Global sections of a proper algebraic space over a field. -/
@[stacks 0DMY] #check (AlgebraicGeometry.AlgebraicSpace.globalSectionsFiniteDimensional :
  ∀ {k : Type u} [Field k] {X : AlgebraicSpace (Spec (of k))} [Proper (SchemeRealization.toBase X)],
    FiniteDimensional k (globalSectionsAlg X))

#check (AlgebraicGeometry.AlgebraicSpace.globalSectionsLocalArtinianFactorization :
  ∀ {k : Type u} [Field k] {X : AlgebraicSpace (Spec (of k))} [Proper (SchemeRealization.toBase X)],
    ∃ (_ : Fintype (ConnectedComponents (Points X)))
      (A : ConnectedComponents (Points X) → Type u)
      (_ : ∀ i, CommRing (A i))
      (_ : ∀ i, Algebra k (A i))
      (_ : ∀ i, IsLocalRing (A i))
      (_ : globalSectionsAlg X ≃ₐ[k] ∀ i, A i),
      ∀ i, IsArtinianRing (A i))

#check (AlgebraicGeometry.AlgebraicSpace.globalSectionsFieldFactorizationOfIsReduced :
  ∀ {k : Type u} [Field k] {X : AlgebraicSpace (Spec (of k))} [Proper (SchemeRealization.toBase X)] [IsReduced X],
    ∃ (_ : Fintype (ConnectedComponents (Points X)))
      (K : ConnectedComponents (Points X) → Type u)
      (_ : ∀ i, Field (K i))
      (_ : ∀ i, Algebra k (K i))
      (_ : globalSectionsAlg X ≃ₐ[k] ∀ i, K i),
      ∀ i, FiniteDimensional k (K i))

#check (AlgebraicGeometry.AlgebraicSpace.globalSectionsSeparableFieldFactorizationOfGeometricallyReduced :
  ∀ {k : Type u} [Field k] {X : AlgebraicSpace (Spec (of k))} [Proper (SchemeRealization.toBase X)] [GeometricallyReduced X],
    ∃ (_ : Fintype (ConnectedComponents (Points X)))
      (K : ConnectedComponents (Points X) → Type u)
      (_ : ∀ i, Field (K i))
      (_ : ∀ i, Algebra k (K i))
      (_ : globalSectionsAlg X ≃ₐ[k] ∀ i, K i),
      ∀ i, FiniteDimensional k (K i) ∧ Algebra.IsSeparable k (K i))

#check (AlgebraicGeometry.AlgebraicSpace.globalSectionsGeometricallyIrreducibleOfGeometricallyConnected :
  ∀ {k : Type u} [Field k] {X : AlgebraicSpace (Spec (of k))} [Proper (SchemeRealization.toBase X)] [GeometricallyConnected X],
    AlgebraicGeometry.GeometricallyIrreducible (globalSectionsSpecMap X))

#check (AlgebraicGeometry.AlgebraicSpace.globalSectionsGeometricallyIrreducibleOfGeometricallyIrreducible :
  ∀ {k : Type u} [Field k] {X : AlgebraicSpace (Spec (of k))} [Proper (SchemeRealization.toBase X)] [GeometricallyIrreducible X],
    AlgebraicGeometry.GeometricallyIrreducible (globalSectionsSpecMap X))

#check (AlgebraicGeometry.AlgebraicSpace.map_bijective_of_geometricallyReduced_geometricallyConnected :
  ∀ {k : Type u} [Field k] {X : AlgebraicSpace (Spec (of k))} [Proper (SchemeRealization.toBase X)] [GeometricallyReduced X] [GeometricallyConnected X],
    Function.Bijective (globalSectionsMap X))

#check (AlgebraicGeometry.AlgebraicSpace.globalSectionsAlgebraMapBijectiveOfGeometricallyIntegral :
  ∀ {k : Type u} [Field k] {X : AlgebraicSpace (Spec (of k))} [Proper (SchemeRealization.toBase X)] [GeometricallyIntegral X],
    Function.Bijective (globalSectionsMap X))

end AlgebraicGeometry.AlgebraicSpace
