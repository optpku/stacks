module

public import ReasLib.RingTheory.Etale.Locus.BaseChange
public import ReasLib.RingTheory.Etale.FiniteProduct
public import ReasLib.RingTheory.Etale.FieldCriterion
public import ReasLib.RingTheory.Etale.FilteredColimit
public import ReasLib.RingTheory.Etale.LocalizationDescent
public import ReasLib.RingTheory.RingHom.Syntomic.Smooth
public import Mathlib.RingTheory.RingHom.Etale
import StacksCheckRecall

/-!
@stack 00U2
-/

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Algebra.TensorProduct
open scoped TensorProduct

universe u v w uJ vJ

namespace Algebra

/-
Domain-style sampling for Lemma 10.143.3:
- primary domain: étale `R`-algebras and their locality, base-change, filtered-colimit, and
  finite-product behavior in commutative algebra;
- sampled owner declarations:
  `Algebra.Etale`,
  `RingHom.Etale.ofLocalizationSpanTarget`,
  `Algebra.Etale.baseChange`,
  `Algebra.Etale.exists_subalgebra_fg`,
  `smooth_is_baseChange_of_stage_of_isColimit`;
- best owner abstraction: `Algebra.Etale` is the algebra-level owner, while
  `RingHom.Etale.ofLocalizationSpanTarget` is the canonical locality owner for target-local
  descent;
- primitive data: an `R`-algebra `S` together with the owner predicate `Etale R S`;
- derived API: locality on principal-open covers, étale loci, syntomicity, flatness, field
  criteria, filtered-colimit descent, localization descent, and finite-product criteria.

Source/core/bridge triage:
- `source-facing`: the textbook clauses (4) through (11), which are bridge statements about how
  étaleness behaves under standard constructions;
- `core/canonical`: `Algebra.Etale` / `RingHom.Etale`;
- `bridge/view`: algebra-level finite-cover formulations, `etaleLocus`, filtered-colimit descent,
  and the syntomic / flat / field criteria consequences.
-/

/- Lemma 10.143.3 (1): for any commutative ring `R` and any element `f : R`, the localization map
`R → R[1 / f]` is étale. This is exactly the canonical theorem
`Algebra.Etale.of_isLocalizationAway`. -/
@[stacks 00U2 "etale principal localization"]
#check @Algebra.Etale.of_isLocalizationAway

/- Companion recall, clause (2): compositions of étale ring maps are étale. This is exactly the
canonical theorem `Algebra.Etale.comp`. -/
@[stacks 00U2 "composition of etale maps"]
#check @Algebra.Etale.comp

/- Companion recall, clause (3): base change preserves étale ring maps. This is exactly the
canonical tensor-product base-change instance `Algebra.Etale.baseChange`. -/
@[stacks 00U2 "base change of etale maps"]
#check @Algebra.Etale.baseChange

/- Clause (4): étaleness is local on the target for principal-open covers. This is exactly the
canonical owner-level locality theorem `RingHom.Etale.ofLocalizationSpanTarget`. -/
@[stacks 00U2 "target-locality of etale maps"]
#check @RingHom.Etale.ofLocalizationSpanTarget

/- Lemma 10.143.3 (00U2), clause (5): after a flat base change `R → R'`,
the etale locus of `R' ⊗[R] S` is the inverse image of the etale locus of
`S`.  The reusable owner supplies both the pointwise and set-theoretic forms. -/
@[stacks 00U2 "flat base change of etale loci"]
#check @Algebra.etaleLocus_preimage_includeRight_eq_baseChange

@[stacks 00U2 "pointwise flat base change of etale loci"]
#check @Algebra.mem_etaleLocus_baseChange_iff

section Syntomic

/- Lemma 10.143.3 (00U2), clause (6): an etale algebra is syntomic.  The
source-facing consequence is the existing smooth-to-syntomic bridge, together
with Mathlib's canonical `Etale` to `Smooth` instance. -/
@[stacks 00U2 "etale maps are syntomic"]
#check @Algebra.Smooth.syntomic

/- The same clause's ``in particular flat'' conclusion is exposed by the
canonical ring-map characterization; specialize it to `algebraMap R S` and
use `RingHom.flat_algebraMap_iff` when a module-level fact is required. -/
@[stacks 00U2 "etale maps are flat"]
#check @RingHom.Etale.iff_flat_and_formallyUnramified

end Syntomic

/- Lemma 10.143.3 (00U2), clause (7): over a field, etaleness is equivalent
to vanishing Kähler differentials.  The shared owner uses the more general
`EssFiniteType` hypothesis. -/
@[stacks 00U2 "etale criterion by Kahler differentials over a field"]
#check @Algebra.Etale.iff_subsingleton_kaehlerDifferential

/- Companion recall, clause (8): every étale algebra descends to an étale model over a finitely
generated `ℤ`-subalgebra of the base. This is exactly
`Algebra.Etale.exists_subalgebra_fg`. -/
@[stacks 00U2 "finite type base model for an etale algebra"]
#check @Algebra.Etale.exists_subalgebra_fg

/- Lemma 10.143.3 (00U2), clause (9): an etale algebra over a filtered
colimit of rings descends to an etale algebra at one stage.  The neutral leaf
also exposes the canonical cocone-leg `stageAlgebra` used by the tensor form. -/
@[stacks 00U2 "etale filtered-colimit descent"]
#check @CommRingCat.FilteredColimit.Etale.exists_stage

#check @CommRingCat.FilteredColimit.stageAlgebra

/- Lemma 10.143.3 (00U2), clause (10): an etale algebra over an arbitrary
localization descends to an etale algebra over the original base.  The shared
owner retains the explicit `Aₛ`-base-change algebra equivalence. -/
@[stacks 00U2 "etale localization descent"]
#check @Algebra.Etale.exists_model_of_localization

/- Lemma 10.143.3 (00U2), clause (11): a binary product of `R`-algebras is
etale over `R` exactly when each factor is etale.  The shared owner is the
more reusable finite-index family criterion, whose binary case is immediate. -/
@[stacks 00U2 "finite products of etale algebras"]
#check @Algebra.Etale.pi_iff

end Algebra
