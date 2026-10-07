module

import StacksCheckRecall
import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Coextension

open CategoryTheory

universe u

/- Example 48.7.3: for a ring map `A →+* B` and `K ∈ D(A)`, the affine trace
`RHom_A(B, K) ⟶ RHom_A(A, K) = K` is the counit of derived restriction–coextension,
after viewing `RHom_A(B, K)` as an object of `D(A)`. -/
@[stacks 0B6L] #check
  (CategoryTheory.ModuleCat.DerivedCoextension.counitApp :
    ∀ {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
      (K : DerivedCategory (ModuleCat.{u, u} A)),
      (ModuleCat.derivedRestrictionOfScalars f).obj
          ((ModuleCat.derivedCoextensionOfScalars f).obj K) ⟶ K)
