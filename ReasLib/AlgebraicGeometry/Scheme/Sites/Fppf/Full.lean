module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Limits
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.ChosenPresentation

/-!
# The full chosen big fppf site

All schemes form a chosen presentation with small fppf covering families.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.ChosenBigFppfSite

/-- A presieve is a small fppf covering if it is the family of a universe-small fppf cover. -/
def smallCovering {target : Scheme.{u}} (family : Presieve target) : Prop :=
  ∃ cover : Scheme.Cover.{u} Scheme.fppfPrecoverage target,
    family = Presieve.ofArrows cover.X cover.f

/-- A singleton isomorphism is a small fppf covering. -/
theorem smallCovering_hasIsos {target source : Scheme.{u}} (arrow : source ⟶ target)
    [IsIso arrow] : smallCovering (Presieve.singleton arrow) :=
  sorry

/-- Pulling back a small fppf covering gives a small fppf covering. -/
theorem smallCovering_pullbacks {target source : Scheme.{u}} (arrow : source ⟶ target)
    (family : Presieve target) (covering : smallCovering family) :
    smallCovering (Presieve.pullbackArrows arrow family) :=
  sorry

/-- Composing small fppf coverings gives a small fppf covering. -/
theorem smallCovering_transitive {target : Scheme.{u}} (family : Presieve target)
    (refinement : ∀ ⦃source⦄ (arrow : source ⟶ target), family arrow → Presieve source)
    (covering : smallCovering family)
    (refinementCovering : ∀ ⦃source⦄ (arrow : source ⟶ target) (membership : family arrow),
      smallCovering (refinement arrow membership)) :
    smallCovering (family.bind refinement) :=
  sorry

/-- The pretopology on schemes whose covering presieves are small fppf covering families. -/
def smallPretopology : Pretopology Scheme.{u} where
  coverings := fun _ ↦ {family | smallCovering family}
  has_isos := fun {target source} arrow ↦
    smallCovering_hasIsos (target := target) (source := source) arrow
  pullbacks := fun {target source} arrow family covering ↦
    smallCovering_pullbacks (target := target) (source := source) arrow family covering
  transitive := fun {target} family refinement covering refinementCovering ↦
    smallCovering_transitive (target := target) family refinement covering refinementCovering

/-- The identity presentation of all schemes with small fppf covers satisfies the chosen-site laws. -/
theorem full_specification :
    IsChosenBigSite Scheme.fppfPrecoverage (Cat.of Scheme.{u})
      (inferInstanceAs (HasPullbacks Scheme.{u}))
      (𝟭 Scheme.{u}) Set.univ (fun _ ↦ {family | smallCovering family}) smallPretopology :=
  sorry

/-- The full chosen fppf presentation has all schemes, the identity functor, and small fppf covers. -/
def full : ChosenBigFppfSite.{u, u + 1} where
  carrier := Cat.of Scheme.{u}
  hasPullbacks := inferInstanceAs (HasPullbacks Scheme.{u})
  toScheme := 𝟭 Scheme.{u}
  fullyFaithful := Functor.FullyFaithful.id Scheme.{u}
  seedSchemes := Set.univ
  seedCoverings := fun _ ↦ {family | smallCovering family}
  pretopology := smallPretopology
  specification := full_specification

/-- The slice topology of the full chosen presentation is the ordinary big fppf topology. -/
theorem full_bigTopology (base : Scheme.{u}) :
    full.bigTopology base = Scheme.fppfTopology.over base :=
  sorry

end AlgebraicGeometry.ChosenBigFppfSite
