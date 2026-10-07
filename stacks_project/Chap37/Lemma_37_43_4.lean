module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.FinitePresentationFactorization
import StacksCheckRecall

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 37.43.4: with the notation and hypotheses of Lemma 37.43.3, if `f` is
locally of finite presentation, the factorization can be chosen with `π` finite
and of finite presentation over `S`. -/
@[stacks 0F2N] #check
  (AlgebraicGeometry.Scheme.Hom.QuasiFinite.exists_openImmersion_finitePresentationFactorization :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [QuasiFinite f] [IsSeparated f]
      [LocallyOfFinitePresentation f] [CompactSpace S] [QuasiSeparatedSpace S],
      ∃ (T : Scheme.{u}) (j : X ⟶ T) (π : T ⟶ S),
        QuasiCompact j ∧ IsOpenImmersion j ∧ IsFinite π ∧
          Scheme.Hom.FinitePresentation π ∧ j ≫ π = f)

end AlgebraicGeometry.Scheme.Hom
