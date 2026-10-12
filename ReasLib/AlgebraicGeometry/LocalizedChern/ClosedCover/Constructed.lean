/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.LocalizedChern.ClosedCover
public import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Actual closed-cover cap descent

On a base-changed closed cover take the sum of the two proper pushforwards.
The operation on its source is (alpha1,alpha2) ↦ ambient.cap(alpha2). It
descends through this specified surjection because the intersection action
vanishes. No bivariant class is chosen from an existence or IsResult predicate.
-/

@[expose] public section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
noncomputable section
universe u

namespace AlgebraicGeometry.LocalizedChern.Constructed

variable {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
  {X : Over S} [LocallyOfFiniteType X.hom]
  {X₁ X₂ : Scheme.{u}} (i₁ : X₁ ⟶ X.left) (i₂ : X₂ ⟶ X.left)
  [hc₁ : IsClosedImmersion i₁] [hc₂ : IsClosedImmersion i₂]

abbrev source₂ : Over S := Over.mk (i₂ ≫ X.hom)

variable (p : ℤ) (ambient : BivariantClass δ (𝟙 (source₂ i₂)) p)

/-- The ambient operation vanishes on every actual test map factoring through
both cover members. This is the source's intersection-vanishing hypothesis,
not a desired property imposed on a newly supplied localized answer. -/
def IntersectionVanishes : Prop :=
  ∀ {V : Over S} [LocallyOfFiniteType V.hom]
    (v₂ : V ⟶ source₂ i₂) [LocallyOfFiniteType v₂.left]
    (v₁ : V.left ⟶ X₁), v₂.left ≫ i₂ = v₁ ≫ i₁ →
      ∀ k : ℤ, ambient.cap v₂ (𝟙 V) v₂ IsPullback.of_id_snd k = 0

variable {V V₂ : Over S} [LocallyOfFiniteType V.hom] [LocallyOfFiniteType V₂.hom]
  (a : V₂ ⟶ source₂ i₂) (j₂ : V₂ ⟶ V) (g : V ⟶ X)
  [LocallyOfFiniteType g.left] (square : IsPullback a.left j₂.left i₂ g.left)

/-- The actual first member of the base-changed cover. -/
def member₁ : Over S := Over.mk (pullback.snd i₁ g.left ≫ V.hom)

def inclusion₁ : member₁ i₁ g ⟶ V := Over.homMk (pullback.snd i₁ g.left)

include hc₁ in
instance member₁_finiteType : LocallyOfFiniteType (member₁ i₁ g).hom := by
  -- Closed immersion base change followed by the given locally-finite-type map.
  sorry

include hc₁ in
instance inclusion₁_proper : IsProper (inclusion₁ i₁ g).left := by
  -- The first inclusion is the displayed base change of the closed immersion.
  sorry

include square hc₂ in
theorem second_proper : IsProper j₂.left := by
  sorry

include square in
theorem second_to_source_finiteType : LocallyOfFiniteType a.left := by
  sorry

/-- The fixed closed-cover surjection, using both actual proper pushforwards. -/
def sumPushforward (k : ℤ) :
    (RelativeChow δ (member₁ i₁ g) k × RelativeChow δ V₂ k) →+ RelativeChow δ V k := by
  letI := second_proper i₂ a j₂ g square
  exact (ChowGroup.map δ (member₁ i₁ g) V (inclusion₁ i₁ g) k).coprod
    (ChowGroup.map δ V₂ V j₂ k)

/-- The specified operation before descending: zero on the first member,
the given ambient operation on the second member. -/
def pairCap (k : ℤ) :
    (RelativeChow δ (member₁ i₁ g) k × RelativeChow δ V₂ k) →+ RelativeChow δ V₂ (k - p) := by
  letI := second_to_source_finiteType i₂ a j₂ g square
  exact (ambient.cap a (𝟙 V₂) a IsPullback.of_id_snd k).comp (AddMonoidHom.snd _ _)

variable (cover : Set.range i₁ ∪ Set.range i₂ = Set.univ)
  (vanishing : IntersectionVanishes δ i₁ i₂ p ambient)

include cover in
/-- The concrete sum map of a closed cover is onto. This is a fixed-map
Chow-generation law; the data of its two summands are already displayed. -/
theorem sumPushforward_surjective (k : ℤ) :
    Function.Surjective (sumPushforward δ i₁ i₂ a j₂ g square k) := by
  sorry

include cover vanishing in
/-- Signed intersection pushforward generates the kernel, and the given
ambient operation vanishes on those intersection contributions. -/
theorem pairCap_kills_kernel (k : ℤ) :
    (sumPushforward δ i₁ i₂ a j₂ g square k).ker ≤
      (pairCap δ i₁ i₂ p ambient a j₂ g square k).ker := by
  sorry

/-- The actual quotient descent. The internal representative choice in
Mathlib's liftOfSurjective is through this fixed sum map; kernel annihilation
proves independence. It does not choose a localized bivariant answer. -/
def descendedCap (k : ℤ) : RelativeChow δ V k →+ RelativeChow δ V₂ (k - p) :=
  (sumPushforward δ i₁ i₂ a j₂ g square k).liftOfSurjective
    (sumPushforward_surjective δ i₁ i₂ a j₂ g square cover k)
    ⟨pairCap δ i₁ i₂ p ambient a j₂ g square k,
      pairCap_kills_kernel δ i₁ i₂ p ambient a j₂ g square cover vanishing k⟩

/-- Quotient evaluation recovers the exact operation on every pair of input classes. -/
theorem descendedCap_sum (k : ℤ)
    (x : RelativeChow δ (member₁ i₁ g) k × RelativeChow δ V₂ k) :
    descendedCap δ i₁ i₂ p ambient a j₂ g square cover vanishing k
      (sumPushforward δ i₁ i₂ a j₂ g square k x) =
        pairCap δ i₁ i₂ p ambient a j₂ g square k x :=
  AddMonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _

/-- The constructed cap family on every actual cartesian base change. -/
def capFamily : BivariantClass.CapFamily δ
    (Over.homMk i₂ : source₂ i₂ ⟶ X) p :=
  fun {_ _} _ _ a j₂ g _ square k =>
    descendedCap δ i₁ i₂ p ambient a j₂ g square cover vanishing k

theorem capFamily_proper : BivariantClass.CompatibleWithProperPushforward δ
    (capFamily δ i₁ i₂ p ambient cover vanishing) := by
  sorry

theorem capFamily_flat : BivariantClass.CompatibleWithFlatPullback δ
    (capFamily δ i₁ i₂ p ambient cover vanishing) := by
  sorry

theorem capFamily_gysin : BivariantClass.CompatibleWithCartierGysin δ
    (capFamily δ i₁ i₂ p ambient cover vanishing) := by
  sorry

/-- A real bivariant class record, whose cap field is the specified quotient descent. -/
def localized : BivariantClass δ (Over.homMk i₂ : source₂ i₂ ⟶ X) p where
  cap := capFamily δ i₁ i₂ p ambient cover vanishing
  map_proper := capFamily_proper δ i₁ i₂ p ambient cover vanishing
  pullback_flat := capFamily_flat δ i₁ i₂ p ambient cover vanishing
  gysin_cartier := capFamily_gysin δ i₁ i₂ p ambient cover vanishing

theorem localized_cap (k : ℤ) (α : RelativeChow δ V k) :
    (localized δ i₁ i₂ p ambient cover vanishing).cap a j₂ g square k α =
      descendedCap δ i₁ i₂ p ambient a j₂ g square cover vanishing k α := rfl

/-- The two source cap laws for this concrete descent. Their proof reduces
to descendedCap_sum at (0,alpha2) and (alpha1,0), respectively. -/
theorem localized_spec : BivariantClass.IsLocalizedExtension δ X i₁ i₂ p ambient
    (localized δ i₁ i₂ p ambient cover vanishing) := by
  sorry

end AlgebraicGeometry.LocalizedChern.Constructed
