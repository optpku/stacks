module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.IdealPrincipalization
import StacksCheckRecall

@[expose] public section

open TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/- Lemma 54.4.1: on a Noetherian scheme, an ideal supported on finitely many closed points
whose local rings are regular of dimension two becomes an invertible ideal sheaf after a finite
sequence of blowups at closed points lying over the given set. -/
@[stacks 0AHH] #check (AlgebraicGeometry.Scheme.existsInvertibleIdealAfterPointBlowups :
  ∀ (X : Scheme.{u}) [IsNoetherian X] (T : Set X),
    T.Finite → T ⊆ closedPoints X →
      (∀ x, x ∈ T → IsRegularLocalRing (X.presheaf.stalk x)) →
        (∀ x, x ∈ T → ringKrullDim (X.presheaf.stalk x) = 2) →
          (I : X.IdealSheafData) → I.supportSet ⊆ T →
            ∃ (Xn : Scheme.{u}) (s : PointBlowupSequence X Xn),
              s.EveryCenterOver T ∧
                IsEffectiveCartierDivisor ((I.comap s.toSource).subschemeι))

end AlgebraicGeometry.Scheme
