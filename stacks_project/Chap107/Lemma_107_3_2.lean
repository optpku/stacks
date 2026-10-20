module

public import ReasLib.AlgebraicGeometry.Scheme.IrreducibleComponent.Multiplicity
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/- Lemma 107.3.2: if `f : U ⟶ X` is a smooth morphism of locally Noetherian schemes,
`T'` is an irreducible component of `U`, and `T` is the irreducible component of `X`
equal to the closure of the image of `T'`, then their multiplicities agree. -/
@[stacks 0DR6] #check
  (AlgebraicGeometry.Scheme.Hom.irreducibleComponentMultiplicity_eq_of_smooth :
    ∀ {U X : Scheme.{u}} [IsLocallyNoetherian U] [IsLocallyNoetherian X]
      (f : U ⟶ X) [Smooth f] (T' : irreducibleComponents U)
      (T : irreducibleComponents X),
      closure (Set.image f.base (T' : Set U)) = (T : Set X) →
        U.irreducibleComponentMultiplicity T' = X.irreducibleComponentMultiplicity T)

end AlgebraicGeometry.Scheme
