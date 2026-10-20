module

public import Mathlib.CategoryTheory.Sites.Pretopology
public import Mathlib.CategoryTheory.Sites.Point.Conservative
public import ReasLib.CategoryTheory.Sites.QuasiCompact
public import ReasLib.CategoryTheory.Sites.Family.CoverLifting
public import ReasLib.CategoryTheory.Sites.Point.Construction

/-!
# Finite refinements of site coverings

The chosen-cover and sieve-saturated versions are separate owners: a chosen cover is additional
presentation data, whereas a Grothendieck topology is already saturated under generated sieves.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.SemiRepresentableFamily.Over

universe w u v q w'

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace Precoverage

/-- A chosen-cover site object has the finite-refinement property when every chosen cover admits
a finite chosen cover which factors through it. -/
class HasFiniteRefinement (K : Precoverage C) (U : C) : Prop where
  finite_refinement (R : Presieve U) (hR : R ∈ K U) :
    ∃ (S : Presieve U), S ∈ K U ∧ S.uncurry.Finite ∧ S.FactorsThru R

/-- A chosen-cover site object has the finite-subcover property when every chosen cover contains a
finite selected subfamily which is still a chosen cover. -/
class HasFiniteSubcover (K : Precoverage C) (U : C) : Prop where
  finite_subcover (R : Presieve U) (hR : R ∈ K U) :
    ∃ (T : Set R.uncurry), T.Finite ∧ R.subfamily T ∈ K U

/-- The finite-refinement property in the fixed-target-family presentation. -/
theorem HasFiniteRefinement.finite_refinement_of_family
    {K : Precoverage C} {U : C} (hU : K.HasFiniteRefinement U)
    (𝒰 : SemiRepresentableFamily.Over.{w} U) (h𝒰 : 𝒰.toPresieve ∈ K U) :
    ∃ (𝒱 : SemiRepresentableFamily.Over.{w} U) (_ : Finite 𝒱.index)
      (_ : 𝒱.toPresieve ∈ K U), Nonempty (𝒱 ⟶ 𝒰) := sorry

/-- A finite chosen subcover induces a finite chosen refinement. -/
theorem HasFiniteSubcover.toFiniteRefinement
    {K : Precoverage C} {U : C} (hU : K.HasFiniteSubcover U) :
    K.HasFiniteRefinement U := sorry

/-- A finite chosen refinement implies chosen-cover quasi-compactness. -/
theorem HasFiniteRefinement.quasiCompact
    {K : Precoverage C} {U : C} (hU : K.HasFiniteRefinement U) :
    K.QuasiCompactObject U := sorry

namespace HasFiniteRefinement.Counterexample

/-- There are chosen-cover sites where quasi-compactness does not imply the finite-refinement
property. The category and pullback structures are existential data, so their `letI` binders are
scoped to the chosen counterexample rather than installed as ambient instances. -/
theorem quasiCompact :
    ∃ (D : Type u) (categoryD : Category.{v} D)
      (pullbacksD : Limits.HasPullbacks D),
      -- Local instance justification (noncanonical choice): The chosen category types the witness.
      letI : Category.{v} D := categoryD
      -- Local instance justification (noncanonical choice): The chosen pullbacks type the witness.
      letI : Limits.HasPullbacks D := pullbacksD
      ∃ (K : Pretopology D) (V : D),
        K.toPrecoverage.QuasiCompactObject V ∧
          ¬ K.toPrecoverage.HasFiniteRefinement V := sorry

end HasFiniteRefinement.Counterexample

namespace HasFiniteSubcover.Counterexample

/-- There are chosen-cover sites where the finite-refinement property does not imply the finite
selected-subcover property. The category and pullback structures are existential data, so their
`letI` binders are scoped to the chosen counterexample rather than installed globally. -/
theorem finiteRefinement :
    ∃ (D : Type u) (categoryD : Category.{v} D)
      (pullbacksD : Limits.HasPullbacks D),
      -- Local instance justification (noncanonical choice): The chosen category types the witness.
      letI : Category.{v} D := categoryD
      -- Local instance justification (noncanonical choice): The chosen pullbacks type the witness.
      letI : Limits.HasPullbacks D := pullbacksD
      ∃ (K : Pretopology D) (V : D),
        K.toPrecoverage.HasFiniteRefinement V ∧
          ¬ K.toPrecoverage.HasFiniteSubcover V := sorry

end HasFiniteSubcover.Counterexample

end Precoverage

namespace GrothendieckTopology

/-- A Grothendieck-topology object has the finite-refinement property when each generated covering
sieve is refined by a finite covering family. -/
@[stacks 00YQ "finite refinement property"]
class HasFiniteRefinement (J : GrothendieckTopology C) (U : C) : Prop where
  finite_refinement (R : Presieve U) (hR : Sieve.generate R ∈ J U) :
    ∃ (𝒱 : SemiRepresentableFamily.Over.{max u v} U) (_ : Finite 𝒱.index)
      (_ : 𝒱.toSieve ∈ J U),
      𝒱.toSieve ≤ Sieve.generate R

/-- A Grothendieck-topology object has the finite-subcover property when every generated covering
sieve contains a finite covering subfamily. -/
class HasFiniteSubcover (J : GrothendieckTopology C) (U : C) : Prop where
  finite_subcover (R : Presieve U) (hR : Sieve.generate R ∈ J U) :
    ∃ (T : Set R.uncurry), T.Finite ∧
      Sieve.ofArrows (fun i : T ↦ i.1.1.1) (fun i ↦ i.1.1.2) ∈ J U

/-- The topology-facing finite-refinement property in the fixed-target-family presentation. -/
theorem HasFiniteRefinement.finite_refinement_of_family
    {J : GrothendieckTopology C} {U : C} (hU : HasFiniteRefinement J U)
    (𝒰 : SemiRepresentableFamily.Over.{w} U) (h𝒰 : 𝒰.toSieve ∈ J U) :
    ∃ (𝒱 : SemiRepresentableFamily.Over.{max u v} U) (_ : Finite 𝒱.index)
      (_ : 𝒱.toSieve ∈ J U),
      𝒱.toSieve ≤ 𝒰.toSieve := sorry

/-- A finite sieve-saturated subcover induces a finite sieve-saturated refinement. -/
theorem HasFiniteSubcover.toFiniteRefinement
    {J : GrothendieckTopology C} {U : C} (hU : HasFiniteSubcover J U) :
    HasFiniteRefinement J U := sorry

/-- A finite sieve-saturated refinement implies sieve-saturated quasi-compactness. -/
theorem HasFiniteRefinement.quasiCompact
    {J : GrothendieckTopology C} {U : C} (hU : HasFiniteRefinement J U) :
    J.QuasiCompactObject U := sorry

namespace HasFiniteRefinement

/-- A site with finite limits and a finite refinement for every covering sieve has enough
points.  The site-wide hypothesis is explicit rather than an ambient instance so that local
applications do not need to install a noncanonical typeclass. -/
theorem hasEnoughPoints
    {J : GrothendieckTopology C} [Limits.HasFiniteLimits C]
    (hJ : ∀ X : C, HasFiniteRefinement J X) :
    HasEnoughPoints.{max (u + 1) (v + 1)} J := sorry

end HasFiniteRefinement

namespace Point.Fiber

/-- Finite-cover lifting becomes lifting along arbitrary covering sieves when every covering
sieve has a finite refinement.  This is the bridge from the finite-family construction used in
refinement arguments to the canonical point-construction condition. -/
theorem of_finite_cover_lifts
    {J : GrothendieckTopology C} {p : C ⥤ Type q}
    (hJ : ∀ X : C, HasFiniteRefinement J X)
    (hp : Functor.FiniteCoverLifts.{u, v, q, w'} p J) :
    coversLift J p := sorry

end Point.Fiber

end GrothendieckTopology

end CategoryTheory
