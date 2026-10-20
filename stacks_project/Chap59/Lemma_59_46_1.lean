module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Extension
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Etale

/- Lemma 59.46.1: For a closed immersion and two schemes étale over the ambient
scheme, every morphism after pullback is induced by a span whose first leg
pulls back to an isomorphism. -/
@[stacks 04FV] #check (AlgebraicGeometry.Etale.exists_extension_of_closedImmersion :
    ∀ {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
      (U U' : X.Etale)
      (h : (Scheme.smallEtalePullback i).obj U ⟶
        (Scheme.smallEtalePullback i).obj U'),
      ∃ (W : X.Etale) (a : W ⟶ U) (b : W ⟶ U')
        (e : (Scheme.smallEtalePullback i).obj W ≅
          (Scheme.smallEtalePullback i).obj U),
        e.hom = (Scheme.smallEtalePullback i).map a ∧
          h = e.inv ≫ (Scheme.smallEtalePullback i).map b)

end AlgebraicGeometry.Etale
