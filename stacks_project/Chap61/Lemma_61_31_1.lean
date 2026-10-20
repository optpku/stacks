module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.Refinement
import StacksCheckRecall

universe u w

open CategoryTheory

/- Lemma 61.31.1: for a big pro-étale site Sch_proétale as in
Definition 61.12.7 and T in that site, every ambient pro-étale covering
{T_i ⟶ T} is refined by some covering {U_j ⟶ T} that lies in the site. -/
@[stacks 098J] #check
  (AlgebraicGeometry.BigProetaleSite.exists_coveringFamily_refining :
    ∀ (X : AlgebraicGeometry.BigProetaleSite.{u}) {T : X.carrier}
      (𝒰 : AlgebraicGeometry.Scheme.Cover.{w}
        AlgebraicGeometry.Scheme.proetalePrecoverage (X.toScheme.obj T)),
      ∃ (J : Type u) (U : J → X.carrier) (f : ∀ j, U j ⟶ T),
        CategoryTheory.Presieve.ofArrows U f ∈ X.pretopology T ∧
          ∃ (a : J → 𝒰.I₀) (g : ∀ j, X.toScheme.obj (U j) ⟶ 𝒰.X (a j)),
            ∀ j, g j ≫ 𝒰.f (a j) = X.toScheme.map (f j))
