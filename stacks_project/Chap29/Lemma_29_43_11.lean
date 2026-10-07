module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Factorization
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 29.43.11: every H-quasi-projective morphism factors as an open immersion followed by an
H-projective morphism. -/
@[stacks 01WA] #check
  (AlgebraicGeometry.HQuasiProjective.exists_factor_openImmersion_hProjective :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ S},
      AlgebraicGeometry.HQuasiProjective f →
        ∃ (X' : AlgebraicGeometry.Scheme.{u}) (i : X ⟶ X') (g : X' ⟶ S)
          (_ : AlgebraicGeometry.IsOpenImmersion i) (_ : AlgebraicGeometry.HProjective g),
            i ≫ g = f)
