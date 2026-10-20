module

public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import ReasLib.RingTheory.GradedAlgebra.DegreeZero
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Algebra structures on homogeneous localizations

This leaf contains only the base-algebra structures on a homogeneous localization.  Module
localization belongs to `Base` and `Module`; keeping the algebra instances here lets algebra-chart
consumers avoid importing the module construction.
-/

@[expose] public section

noncomputable section

universe u v w

namespace HomogeneousLocalization.Algebra

variable {ι : Type u} [AddCommMonoid ι] [DecidableEq ι]
variable {R : Type v} {S : Type w}
-- A `Submodule R S` is an additive subgroup only when the scalar ring supplies negation;
-- this is the boundary required by Mathlib's homogeneous-localization carrier.
variable [CommRing R] [CommRing S] [Algebra R S]
variable (𝒜 : ι → Submodule R S) [GradedAlgebra 𝒜]

/-- Every homogeneous localization is an `R`-algebra through its degree-zero piece. -/
@[stacks 00JR "base algebra on a homogeneous localization"]
noncomputable instance instAlgebra (P : Submonoid S) :
    Algebra R (HomogeneousLocalization 𝒜 P) where
  -- Reuse Mathlib's canonical localization action.  Rebuilding this action through
  -- `Algebra.compHom` is propositionally equal but breaks definitional scalar-tower reuse.
  smul := (HomogeneousLocalization.instSMul P).smul
  algebraMap :=
    (algebraMap (𝒜 0) (HomogeneousLocalization 𝒜 P)).comp (algebraMap R (𝒜 0))
  commutes' := sorry
  smul_def' := sorry

/-- The external base ring, the degree-zero graded piece, and a homogeneous localization form a
scalar tower.  This is the localization-specific companion to
`SetLike.GradeZero.instIsScalarTower`. -/
@[stacks 00JR "base and homogeneous-localization scalar tower"]
instance instScalarTower (P : Submonoid S) :
    IsScalarTower R (𝒜 0) (HomogeneousLocalization 𝒜 P) := sorry

end HomogeneousLocalization.Algebra
