module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Ample

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.QuasiProjective

/- Lemma 37.49.1: for a morphism to a scheme admitting an ample invertible module,
quasi-projectivity, H-quasi-projectivity, projective compactifiability, finite type with an
ample invertible module on the source, and finite type with a relatively very ample module are
equivalent. -/
@[stacks 0B42]
#check (AlgebraicGeometry.QuasiProjective.tfae_of_hasAmpleInvertibleModule :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S),
    Scheme.Modules.HasAmpleInvertibleModule S →
      List.TFAE [
        QuasiProjective f,
        HQuasiProjective f,
        ∃ (X' : Scheme.{u}) (i : X ⟶ X') (g : X' ⟶ S)
          (_ : QuasiCompact i) (_ : IsOpenImmersion i) (_ : Projective g),
          i ≫ g = f,
        Scheme.Hom.FiniteType f ∧ Scheme.Modules.HasAmpleInvertibleModule X,
        Scheme.Hom.FiniteType f ∧ ∃ L : X.Modules, RelativelyVeryAmple f L])

end AlgebraicGeometry.QuasiProjective
