module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.GroupoidScheme.Module.Quasicoherent.CardinalGeneration.Small

@[expose] public section

open CategoryTheory

universe u

/- Lemma 39.15.6 -/
@[stacks 077T] #check
  (AlgebraicGeometry.GroupoidScheme.QCoh.exists_set_kappaGenerated_representatives :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      (G : AlgebraicGeometry.GroupoidScheme S) (κ : Cardinal.{u}),
      ∃ T : Set G.QCoh,
        (∀ E ∈ T, E.obj.obj.IsKappaGenerated κ) ∧
          ∀ E : G.QCoh, E.obj.obj.IsKappaGenerated κ →
            ∃ E' ∈ T, Nonempty (E' ≅ E))
