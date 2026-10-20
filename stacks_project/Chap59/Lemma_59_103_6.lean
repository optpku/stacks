module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.H.Adjunction
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.HComparison
open CategoryTheory.GrothendieckTopology

noncomputable section

universe u

/- Lemma 59.103.6: for a scheme `X` and `K` in `D⁺(X_étale)` with torsion cohomology sheaves,
the derived adjunction unit `K ⟶ Ra_{X,*} (a_X⁻¹ K)` is an isomorphism, where
`a_X : Sh((Sch/X)_h) ⟶ Sh(X_étale)` is the composite `π_X ∘ ε_X`. -/
@[stacks 0EWG] #check (AlgebraicGeometry.Scheme.HComparison.plusAAdjunction_unit_isIso :
  ∀ {X : Scheme.{u}}
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})),
    DerivedCategory.Plus.cohomologyIn (Sheaf.torsion X.smallEtaleTopology) K →
      IsIso ((plusAAdjunction X).unit.app K))

end

end
