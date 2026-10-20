module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.FlatNotOpen
import ReasLib.RingTheory.Flat.NonProjective
import StacksCheckRecall

@[expose] public section

universe u v

/- Lemma 110.33.1 (1): there exists a ring `R` and a finite flat `R`-module `M` which is
not projective. -/
@[stacks 05FY] #check (Module.exists_finite_flat_not_projective :
    ∃ (R : Type u) (_ : CommRing R) (M : Type v) (_ : AddCommGroup M) (_ : Module R M),
      Module.Finite R M ∧ Module.Flat R M ∧ ¬ Module.Projective R M)

/- Lemma 110.33.1 (2): there exists a closed immersion which is flat but not open. -/
@[stacks 05FY] #check (AlgebraicGeometry.exists_isClosedImmersion_flat_not_isOpenMap :
    ∃ (X Y : AlgebraicGeometry.Scheme.{u}) (f : X ⟶ Y),
      AlgebraicGeometry.IsClosedImmersion f ∧ AlgebraicGeometry.Flat f ∧
        ¬ IsOpenMap f.base)
