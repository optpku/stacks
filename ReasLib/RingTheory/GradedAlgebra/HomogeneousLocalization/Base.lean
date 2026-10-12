/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.GradedAlgebra.HomogeneousLocalization.Algebra
public import ReasLib.RingTheory.GradedAlgebra.HomogeneousLocalization.Module.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Base-ring structures on homogeneous localizations

This leaf is the base-change companion to the module degree-zero construction.  The algebra
instances live in the narrower `Algebra` leaf; this file adds the module bridge and the finite-type
specialization while retaining the historical `Base` import path.
-/

@[expose] public section

noncomputable section

universe u v w x

namespace HomogeneousLocalization.Base

variable {ι : Type u} [AddCommMonoid ι] [DecidableEq ι]
variable {R : Type v} {S : Type w}
-- The base module factors through the homogeneous-localization algebra, so use the same
-- additive-subgroup grading boundary as `HomogeneousLocalization.Algebra`.
variable [CommRing R] [CommRing S] [Algebra R S]

/-- The canonical `R`-module structure on an ordinary localization obtained by first acting
through the homogeneous localization.

This is a named bridge rather than a global instance.  Mathlib also has an `R`-module instance
for `LocalizedModule P M` obtained directly from an existing `R`-module structure on `M`; the two
actions need not be definitionally equal, so registering both globally would make scalar-action
inference ambiguous. -/
@[reducible, stacks 00JR "base module on an ordinary localization"]
noncomputable def moduleOverBase (𝒜 : ι → Submodule R S) [GradedAlgebra 𝒜]
    {M : Type x} [AddCommMonoid M] [Module S M]
    (P : Submonoid S) : Module R (LocalizedModule P M) :=
  Module.compHom (LocalizedModule P M)
    (algebraMap R (HomogeneousLocalization 𝒜 P))

/-- The scalar tower for `moduleOverBase`: the base ring acts through the homogeneous localization
on the localized module.  The target scalar action is named explicitly so the theorem does not
expose Mathlib's independent direct-localization module instance. -/
@[stacks 00JR "base and homogeneous-localization scalar tower"]
theorem scalarTowerOverBase (𝒜 : ι → Submodule R S) [GradedAlgebra 𝒜]
    {M : Type x} [AddCommMonoid M] [Module S M]
    (P : Submonoid S) :
    @IsScalarTower R (HomogeneousLocalization 𝒜 P) (LocalizedModule P M)
      _ _ (moduleOverBase 𝒜 P).toSMul := sorry

end HomogeneousLocalization.Base

namespace HomogeneousLocalization.Away

variable {ι : Type w} [AddCommMonoid ι] [DecidableEq ι]
variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S]
variable (𝒜 : ι → Submodule R S) [GradedAlgebra 𝒜]

/-- If the graded algebra is finite type over `R`, then its homogeneous localization away from any
chosen homogeneous component is finite type over `R`. -/
@[stacks 07Z2 "finite type of a homogeneous localization"]
theorem finiteType_over [Algebra.FiniteType R S] {d : ι} (f : 𝒜 d) :
    Algebra.FiniteType R (HomogeneousLocalization.Away 𝒜 (f : S)) := sorry

end HomogeneousLocalization.Away
