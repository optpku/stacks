module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Ample

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Projective

/- Lemma 37.50.1: for `f : X ⟶ S`, where `S` has an ample invertible module, the following
are equivalent: (1) `Projective f`; (2) `HProjective f`; (3) `QuasiProjective f` and
`IsProper f`; (4) `HQuasiProjective f` and `IsProper f`; (5) `IsProper f` and `X` has an ample
invertible module; (6) `IsProper f` and some module on `X` is relatively ample over `f`;
(7) `IsProper f` and some module on `X` is relatively very ample over `f`; (8) `f` admits a
finite degree-one-generated relative-projective-spectrum presentation whose degree-one module
is of finite type. -/
@[stacks 0B45] #check
  (AlgebraicGeometry.Projective.tfae_of_hasAmpleInvertibleModule :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S)
      (hS : Scheme.Modules.HasAmpleInvertibleModule S),
      List.TFAE [
        Projective f,
        HProjective f,
        QuasiProjective f ∧ IsProper f,
        HQuasiProjective f ∧ IsProper f,
        IsProper f ∧ Scheme.Modules.HasAmpleInvertibleModule X,
        IsProper f ∧ ∃ L : X.Modules, RelativelyAmple f L,
        IsProper f ∧ ∃ L : X.Modules, RelativelyVeryAmple f L,
        ∃ P : Scheme.Hom.RelativeProjPresentation f,
          P.GeneratedByDegreeOneFinite ∧ (P.degreePiece 1).IsFiniteType])

end AlgebraicGeometry.Projective
