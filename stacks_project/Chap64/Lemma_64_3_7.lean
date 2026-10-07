module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.GaloisAction

/-!
# Lemma 64.3.7

The identification of the stalk `(R^j α_* F)_{Spec(k̄)}` with geometric étale
cohomology `H^j(X_{k̄}, F|_{X_{k̄}})` from Theorem 59.53.1 is an isomorphism of
`G_k`-modules.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 64.3.7 -/
@[stacks 03ST] #check
  (AlgebraicGeometry.Scheme.Etale.higherDirectImageStalk_isog_geometricEtaleCohomology :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k)
      (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) (j : ℕ)
      [Finite k] [QuasiCompact X.hom] [QuasiSeparated X.hom],
      ∃ comparison : higherDirectImageStalkGaloisModule X F j ≅
          geometricEtaleCohomologyGaloisModule X F j,
        comparison.hom.hom = higherDirectImageStalkComparison X F j)

end

end
