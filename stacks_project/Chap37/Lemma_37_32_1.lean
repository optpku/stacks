module

public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.GeometricallyIrreducible.LinearForm
import StacksCheckRecall

@[expose] public section

open scoped BigOperators

universe u

/- Lemma 37.32.1: if the coordinates, a linear form with coefficients `g`, and a
`k`-linear combination of the coefficients are jointly algebraically independent over `k`,
then the rational function field over `K` is geometrically irreducible over the field generated
over `k` by the coordinates and the linear form. -/
@[stacks 0G4D]
#check (AlgebraicGeometry.FieldExtension.GeometricallyIrreducible.of_algebraicIndependent_linearForm :
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
    [Algebra.EssFiniteType k K]
    [AlgebraicGeometry.GeometricallyIrreducible
      (AlgebraicGeometry.FieldExtension.specMap k K)]
    (n : ℕ) (hn : 0 < n) (g : Fin n → K) (c : Fin n → k),
    let E := FractionRing (MvPolynomial (Fin n) K)
    let x : Fin n → E :=
      fun i ↦ algebraMap (MvPolynomial (Fin n) K) E (MvPolynomial.X i)
    let ℓ : E := ∑ i, algebraMap K E (g i) * x i
    let d : E := algebraMap K E (∑ i, algebraMap k K (c i) * g i)
    let independentFamily : Sum (Fin n) (Fin 2) → E :=
      Sum.elim x (Fin.cases ℓ (fun _ ↦ d))
    let baseGenerators : Option (Fin n) → E := fun o ↦ o.elim ℓ x
    AlgebraicIndependent k independentFamily →
      AlgebraicGeometry.GeometricallyIrreducible
        (AlgebraicGeometry.FieldExtension.specMap
          (IntermediateField.adjoin k (Set.range baseGenerators)) E))
