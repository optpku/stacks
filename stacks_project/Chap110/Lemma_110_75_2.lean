module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.Counterexamples
import StacksCheckRecall

/-!
# Affine formal algebraic spaces whose regular functions do not separate points
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/- Lemma 110.75.2: there exists an affine formal algebraic space whose regular
functions do not separate points: some directed affine thickening presentation as
in Definition 87.9.1 has inverse-limit global sections a field, while the reduced
space has infinitely many points. -/
@[stacks 0CBD] #check
  (AlgebraicGeometry.exists_isAffineFormalAlgebraicSpace_regularFunctions_not_separatePoints :
    ∃ (𝒮 : ChosenBigFppfSite.{u, u+1}) (S : 𝒮.carrier)
      (_ : HasWeakSheafify (𝒮.bigTopology S) (Type (u+1)))
      (_ : HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (u+1))))
      (X : Sheaf (𝒮.bigTopology S) (Type (u+1))),
      IsAffineFormalAlgebraicSpace X ∧
        ∃ (Λ : Type (u+1)) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
          (D : Λ ⥤ 𝒮.bigAffineSite S),
          IsDirectedAffineThickeningColimit D X ∧
            IsField (limitGlobalSections D) ∧
              ∃ i : Λ, Infinite ((𝒮.bigAffineToScheme S).obj (D.obj i)))

end AlgebraicGeometry
