module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.Factorization
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 32.9.3: let `f : X ⟶ S` be locally of finite type; assume `X` is quasi-compact,
`X` is quasi-separated, plus `S` is quasi-separated. Then `f` factors over `S` through a
closed immersion `X ⟶ X'`, where `X' ⟶ S` is of finite presentation. -/
@[stacks 01ZG] #check
  (AlgebraicGeometry.Scheme.Hom.FinitePresentation.exists_closedImmersion_factorization_of_locallyOfFiniteType :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [CompactSpace X.carrier]
      [QuasiSeparatedSpace X.carrier] [QuasiSeparatedSpace S.carrier],
      (MorphismProperty.comp @IsClosedImmersion
        (@Scheme.Hom.FinitePresentation : MorphismProperty Scheme)) f)
