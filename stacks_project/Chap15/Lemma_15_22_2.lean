module

public import ReasLib.Algebra.Module.Torsion.Characterizations
import StacksCheckRecall

/-!
@stack 0537
-/

@[expose] public section

universe u v w

/-
Domain-style sampling:
- primary domain: torsion theory for modules over commutative rings and its domain specialization;
- sampled owner API:
  `Submodule.torsion`,
  `Submodule.isTorsionFree_iff_torsion_eq_bot`,
  `Submodule.QuotientTorsion.torsion_eq_bot`,
  the quotient torsion-free instance on `M ⧸ Submodule.torsion R M`;
- source-facing: the torsion submodule and the torsion-free quotient by it;
- core/canonical: the mathlib owners `Submodule.torsion` and `Module.IsTorsionFree`;
- bridge/view: none.

Primitive data are only the module over the base ring. The torsion-free structure on the quotient by
`Submodule.torsion R M` is derived API already owned upstream, with proposition-level owner
`Module.IsTorsionFree R (M ⧸ Submodule.torsion R M)` and implementation supplied by
`Submodule.QuotientTorsion.instIsTorsionFree`. The public entry here should expose the
proposition-level owner rather than the internal instance name.
-/

/- Lemma 15.22.2 (1): for a domain `R` with fraction field `K`, the torsion submodule of `M`
is the kernel of the canonical map `M → M ⊗[R] K`. -/
@[stacks 0537 "(1) torsion as the generic-fiber kernel"]
#check @Submodule.torsion_eq_ker_tensorFractionField

section

open Module

variable {R : Type u} [CommRing R] [IsDomain R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/- Lemma 15.22.2 (2): the torsion elements form the canonical submodule
`Submodule.torsion R M`. -/
@[stacks 0537 "(2) torsion submodule"]
#check fun (R : Type u) (M : Type v) [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] => Submodule.torsion R M

/- Lemma 15.22.2 (3): the quotient of an `R`-module by its torsion submodule is torsion free. -/
@[stacks 0537 "(3) torsion-free quotient"]
#check (inferInstance : IsTorsionFree R (M ⧸ Submodule.torsion R M))

end

/- The torsion-submodule owner itself is defined under weaker semiring assumptions. -/
#check Submodule.torsion
