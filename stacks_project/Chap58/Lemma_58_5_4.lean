module

public import ReasLib.AlgebraicGeometry.Scheme.RelativeHom.FiniteEtale
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

/- Lemma 58.5.4: finite étale objects `U` and `V` over `X` admit a finite étale
object representing their relative morphisms, compatibly with every base change. -/
@[stacks 0BL7] #check (AlgebraicGeometry.Scheme.exists_finiteEtaleHom :
  ∀ {X : Scheme.{u}} (U V : AlgebraicGeometry.Scheme.FiniteEtale X),
    ∃ W : AlgebraicGeometry.Scheme.FiniteEtale X,
      Nonempty
        ((AlgebraicGeometry.Scheme.RelativeHom.functor
            (CategoryTheory.Over.mk U.hom) (CategoryTheory.Over.mk V.hom)).RepresentableBy
          (CategoryTheory.Over.mk W.hom)))
