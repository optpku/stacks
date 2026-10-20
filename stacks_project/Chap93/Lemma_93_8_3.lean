module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.FormalDeformation.FlatAlgebra.Tangent

/-!
# Tangent space and infinitesimal automorphisms of algebra deformations
-/

public section

universe u

/- Lemma 93.8.3 (1)
For an arbitrary commutative k-algebra P, tangent classes of flat deformations
are classified by Ext¹ of the naive cotangent complex. -/
@[stacks 0DY3] #check (FlatAlgebraCat.ofExtClass_bijective :
  ∀ (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] (P : Type u) [CommRing P] [Algebra k P],
    Function.Bijective (FlatAlgebraCat.ofExtClass Λ k P :
      RingHom.SquareZeroExtension.extOneNaiveCotangent k P P →
        CategoryTheory.Functor.tangentSpace (FlatAlgebraCat.deformationForget Λ k P)))

/- Lemma 93.8.3 (2)
Infinitesimal automorphisms of the trivial deformation are classified by
k-derivations of P into itself. -/
@[stacks 0DY3] #check (FlatAlgebraCat.infAutOfDerivation_bijective :
  ∀ (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] (P : Type u) [CommRing P] [Algebra k P],
    Function.Bijective (FlatAlgebraCat.infAutOfDerivation Λ k P :
      Derivation k P P → CategoryTheory.Aut (FlatAlgebraCat.trivialDeformationFiber Λ k P)))
