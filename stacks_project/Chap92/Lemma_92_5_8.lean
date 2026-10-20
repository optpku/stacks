module

public import ReasLib.RingTheory.CotangentComplex.Transitivity
public import ReasLib.Algebra.PolynomialSite
import StacksCheckRecall

/-!
# Transitivity triangle for a polynomial algebra

Lemma 92.5.8 records that the canonical transitivity triangle of cotangent
complexes is distinguished in `D(C)` when the intermediate algebra is polynomial.
-/

@[expose] public section

open Algebra
open CategoryTheory
open CategoryTheory.Pretriangulated

universe u

namespace Algebra.CotangentComplex

section

variable (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [Algebra.IsPolynomial A B]

/- Lemma 92.5.8. Let `A → B → C` be ring maps. If `B` is a polynomial algebra over `A`,
then the canonical triangle
`L_{B/A} ⊗ᴸ_B C ⟶ L_{C/A} ⟶ L_{C/B} ⟶ (L_{B/A} ⊗ᴸ_B C)[1]`
is distinguished in `D(C)`. -/
@[stacks 08SA] #check
  (Algebra.CotangentComplex.transitivityTriangle_distinguished A B C :
    Algebra.CotangentComplex.transitivityTriangle A B C ∈
      distTriang (DerivedCategory (ModuleCat.{u} C)))

#check (Algebra.CotangentComplex.tensorDerivedIso A B C :
  (ModuleCat.derivedExtensionOfScalars (algebraMap B C)).obj
      (Algebra.CotangentComplex.derived A B) ≅
    Algebra.CotangentComplex.tensor A B C)

end

section

variable (A : Type u) (σ : Type u) (C : Type u) [CommRing A] [CommRing C]
    [Algebra (MvPolynomial σ A) C] [Algebra A C]
    [IsScalarTower A (MvPolynomial σ A) C]

/- The transitivity triangle for `A → MvPolynomial σ A → C` is distinguished in `D(C)`. -/
#check (Algebra.CotangentComplex.transitivityTriangle_distinguished A (MvPolynomial σ A) C :
  Algebra.CotangentComplex.transitivityTriangle A (MvPolynomial σ A) C ∈
    distTriang (DerivedCategory (ModuleCat.{u} C)))

end

end Algebra.CotangentComplex
