module

public import ReasLib.AlgebraicGeometry.Scheme.RationalMap.Modification
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 31.36.2: Let `S` be a scheme and let `X` and `Y` be schemes over `S`, with `X`
Noetherian and `Y` proper over `S`. Every `S`-partial map from `X` to `Y` extends after a proper
replacement of `X` that is an isomorphism over the partial map's domain. -/
@[stacks 0C4V] #check
  (AlgebraicGeometry.Scheme.PartialMap.exists_properModification :
    ∀ {S X Y : AlgebraicGeometry.Scheme.{u}} [X.Over S] [Y.Over S]
      [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsProper (Y ↘ S)]
      (f : X.PartialMap Y) [f.IsOver S],
      ∃ (X' : AlgebraicGeometry.Scheme.{u}) (p : X' ⟶ X) (f' : X' ⟶ Y),
        AlgebraicGeometry.IsProper p ∧
          IsIso (p ∣_ f.domain) ∧
            f' ≫ (Y ↘ S) = p ≫ (X ↘ S) ∧
              (p ⁻¹ᵁ f.domain).ι ≫ f' = (p ∣_ f.domain) ≫ f.hom)
