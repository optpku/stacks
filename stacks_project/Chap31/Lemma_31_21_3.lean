module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion.Noetherian
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory

universe u

/- Lemma 31.21.3: for an immersion into a locally Noetherian scheme, regular,
Koszul-regular, `H₁`-regular, and quasi-regular are equivalent. -/
@[stacks 063L] #check
  (AlgebraicGeometry.immersionRegularity_tfae :
    ∀ {X Z : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] [IsLocallyNoetherian X],
      List.TFAE
        [ IsRegularImmersion i
        , IsKoszulRegularImmersion i
        , IsH1RegularImmersion i
        , IsQuasiRegularImmersion i
        ])
