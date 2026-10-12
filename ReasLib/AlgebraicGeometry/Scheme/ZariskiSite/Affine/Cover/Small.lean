/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.Pretopology
public import ReasLib.AlgebraicGeometry.Scheme.ZariskiSite.Affine.Cover.Basic

/-!
# Standard covers on the small affine Zariski site

This leaf turns finite distinguished-open covers inside an affine open into a
pretopology on the small affine Zariski carrier with arbitrary inclusions.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.ObjectProperty
open scoped BigOperators

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable (S : Scheme.{u})

/-- A standard Zariski cover of an affine open, viewed in the small affine
Zariski site. The underlying cover data is `StandardZariskiCover.OnAffineOpen`. -/
@[stacks 020T "small affine standard cover"]
abbrev SmallAffineZariskiStandardCover (U : S.smallAffineZariskiSite) :=
  StandardZariskiCover.OnAffineOpen.{u, u} S ⟨U.obj, U.property⟩

namespace SmallAffineZariskiStandardCover

/-- The `i`-th distinguished-open member of a small affine Zariski standard
cover, viewed as an affine open of `S`. -/
def siteObj {U : S.smallAffineZariskiSite}
    (𝒰 : SmallAffineZariskiStandardCover S U) (i : 𝒰.index) : S.smallAffineZariskiSite where
  obj := (StandardZariskiCover.OnAffineOpen.affineOpen 𝒰 i).1
  property := (StandardZariskiCover.OnAffineOpen.affineOpen 𝒰 i).2

/-- The inclusion of the `i`-th distinguished-open member into its small
affine Zariski target. -/
def siteMap {U : S.smallAffineZariskiSite}
    (𝒰 : SmallAffineZariskiStandardCover S U) (i : 𝒰.index) :
    siteObj S 𝒰 i ⟶ U :=
  ObjectProperty.homMk <|
    homOfLE (StandardZariskiCover.OnAffineOpen.affineOpen_le 𝒰 i)

/-- Applying the affine-open inclusion to a standard-cover object recovers
the distinguished open in `S.Opens`. -/
@[simp] theorem toOpens_siteObj {U : S.smallAffineZariskiSite}
    (𝒰 : SmallAffineZariskiStandardCover S U) (i : 𝒰.index) :
    (smallAffineZariskiToOpens S).obj (siteObj S 𝒰 i) = 𝒰.opens i := sorry

/-- Applying the affine-open inclusion to a standard-cover map recovers the
corresponding inclusion of distinguished opens. -/
@[simp] theorem toOpens_siteMap {U : S.smallAffineZariskiSite}
    (𝒰 : SmallAffineZariskiStandardCover S U) (i : 𝒰.index) :
    (smallAffineZariskiToOpens S).map (siteMap S 𝒰 i) =
      homOfLE (StandardZariskiCover.OnAffineOpen.affineOpen_le 𝒰 i) := sorry

/-- The presieve represented by a small affine Zariski standard cover. -/
def presieve {U : S.smallAffineZariskiSite}
    (𝒰 : SmallAffineZariskiStandardCover S U) : Presieve U :=
  Presieve.ofArrows (siteObj S 𝒰) (siteMap S 𝒰)

/-- The distinguished opens of a small affine standard cover have supremum
equal to its target affine open. -/
theorem iSup_eq {U : S.smallAffineZariskiSite}
    (𝒰 : SmallAffineZariskiStandardCover S U) :
    (⨆ i : 𝒰.index, 𝒰.opens i) = U.obj := sorry

end SmallAffineZariskiStandardCover

/-- A presieve on the small affine Zariski site is a standard-covering
presieve when it is represented by a finite distinguished open cover inside
its target affine open. -/
@[stacks 020T]
def smallAffineZariskiCovering {U : S.smallAffineZariskiSite} (R : Presieve U) : Prop :=
  ∃ 𝒰 : SmallAffineZariskiStandardCover S U, R = SmallAffineZariskiStandardCover.presieve S 𝒰

/-- A standard small affine Zariski cover presents a covering presieve. -/
theorem smallAffineZariskiCovering_ofStandardCover {U : S.smallAffineZariskiSite}
    (𝒰 : SmallAffineZariskiStandardCover S U) :
    smallAffineZariskiCovering S (SmallAffineZariskiStandardCover.presieve S 𝒰) := sorry

/-- The small affine Zariski covering predicate unfolds to its finite
standard-cover presentation. -/
theorem smallAffineZariskiCovering_iff {U : S.smallAffineZariskiSite} {R : Presieve U} :
    smallAffineZariskiCovering S R ↔
      ∃ 𝒰 : SmallAffineZariskiStandardCover S U,
        R = SmallAffineZariskiStandardCover.presieve S 𝒰 := sorry

/-- Singleton isomorphisms are covering presieves for the small affine
Zariski standard-cover presentation. -/
theorem smallAffineZariskiCovering_hasIsos :
    ∀ ⦃U V : S.smallAffineZariskiSite⦄ (f : V ⟶ U) [IsIso f],
      smallAffineZariskiCovering S (Presieve.singleton f) := sorry

/-- Small affine standard Zariski covering presieves are stable under
pullback. -/
theorem smallAffineZariskiCovering_pullbacks :
    ∀ ⦃U V : S.smallAffineZariskiSite⦄ (f : V ⟶ U) (R : Presieve U),
      smallAffineZariskiCovering S R →
        smallAffineZariskiCovering S (Presieve.pullbackArrows f R) := sorry

/-- Small affine standard Zariski covering presieves are stable under
refinement. -/
theorem smallAffineZariskiCovering_transitive :
    ∀ ⦃U : S.smallAffineZariskiSite⦄ (R : Presieve U)
      (Ti : ∀ ⦃V⦄ (f : V ⟶ U), R f → Presieve V),
      smallAffineZariskiCovering S R →
        (∀ ⦃V⦄ (f : V ⟶ U) (hR : R f), smallAffineZariskiCovering S (Ti f hR)) →
          smallAffineZariskiCovering S (Presieve.bind R Ti) := sorry

/-- The pretopology on affine opens of `S` generated by finite standard Zariski
covers. -/
@[stacks 020T]
def smallAffineZariskiPretopology : Pretopology S.smallAffineZariskiSite where
  coverings := fun _ ↦ { R | smallAffineZariskiCovering S R }
  has_isos := smallAffineZariskiCovering_hasIsos S
  pullbacks := smallAffineZariskiCovering_pullbacks S
  transitive := smallAffineZariskiCovering_transitive S

/-- The precoverage underlying the standard small affine Zariski
pretopology. -/
abbrev smallAffineZariskiPrecoverage : Precoverage S.smallAffineZariskiSite :=
  (smallAffineZariskiPretopology S).toPrecoverage

/-- Membership in the standard small affine Zariski precoverage is exactly
the finite distinguished-open covering predicate. -/
theorem mem_smallAffineZariskiPrecoverage_iff {U : S.smallAffineZariskiSite} {R : Presieve U} :
    R ∈ smallAffineZariskiPrecoverage S U ↔ smallAffineZariskiCovering S R := sorry

/-- The small affine Zariski topology generated by standard distinguished-open
coverings. -/
@[stacks 020T]
abbrev smallAffineZariskiTopology : GrothendieckTopology S.smallAffineZariskiSite :=
  (smallAffineZariskiPretopology S).toGrothendieck

/-- The small affine Zariski topology is generated by its standard-cover
pretopology. -/
theorem smallAffineZariskiTopology_def :
    smallAffineZariskiTopology S = (smallAffineZariskiPretopology S).toGrothendieck := sorry

/-- Every standard small affine Zariski covering presieve belongs to the
ambient topology-on-opens precoverage restricted to affine opens. -/
theorem smallAffineZariskiCovering_mem_restrictedPrecoverage
    {U : S.smallAffineZariskiSite} {R : Presieve U} (hR : smallAffineZariskiCovering S R) :
    R ∈ smallAffineZariskiRestrictedPrecoverage S U := sorry

end AlgebraicGeometry.Scheme
