module

public import ReasLib.AlgebraicGeometry.Scheme.UniversalFiniteFree
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- Example 49.11.2: the universal affine morphism `π_d : Y_d ⟶ X_d` associated to
the finite free `A_d`-algebra `B_d` of rank `d`. -/
@[stacks 0FKZ] #check
  (UniversalFiniteFreeAlgebra.projection :
    ∀ d : ℕ+, UniversalFiniteFreeAlgebra.familyScheme d ⟶
      UniversalFiniteFreeAlgebra.baseScheme d)

#check (UniversalFiniteFreeAlgebra.CoefficientRing : ℕ+ → Type)
#check (UniversalFiniteFreeAlgebra.UniversalAlgebra : ℕ+ → Type)
#check (UniversalFiniteFreeAlgebra.projectionIsFiniteLocallyFreeOfRank :
  ∀ d : ℕ+, AlgebraicGeometry.IsFiniteLocallyFreeOfRank
    (UniversalFiniteFreeAlgebra.projection d) d)
