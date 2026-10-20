module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.AdditiveAdjunction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening

/-!
# The additive counit along a thickening

Topological invariance of the étale site makes base-change restriction fully
faithful on sheaves. Its inverse on morphisms is dense-site sheaf gluing, and
the inverse of the geometric counit is the preimage of the geometric unit.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace.EtaleAdditive.Thickening

variable {S : Scheme.{u}} {X X' : AlgebraicSpace S} (i : X ⟶ X')
variable [IsThickening i]

/-- The source's étale charts are covered by reductions of target étale charts.
This is the covering part of Stacks' thickening-equivalence lemma, followed by
the usual scheme-chart cover of a spaces-étale object. -/
theorem baseChangeCoverDense : (etaleBaseChange i).IsCoverDense (spacesEtaleTopology X) :=
  sorry

/-- Maps between reductions of étale charts lift locally across the thickening.
This is the fully faithful part of Stacks' topological-invariance theorem. -/
theorem baseChangeLocallyFull : (etaleBaseChange i).IsLocallyFull (spacesEtaleTopology X) :=
  sorry

/-- Dense-site amalgamation reconstructs an additive sheaf map from its actual
base-change restrictions. Its two reconstruction laws are the proved gluing laws. -/
def restrictionFullyFaithful :
    ((etaleBaseChange i).sheafPushforwardContinuous AddCommGrpCat.{u}
      (smallEtaleTopology X') (spacesEtaleTopology X)).FullyFaithful := by
  -- Local instance justification (defeq pin): use the source-justified covering law for this exact base-change family in sheaf gluing.
  letI := baseChangeCoverDense i
  -- Local instance justification (defeq pin): use local lifting of chart morphisms for the same base-change family.
  letI := baseChangeLocallyFull i
  exact
    { preimage := fun α ↦ ⟨Functor.IsCoverDense.sheafHom α.hom⟩
      map_preimage := fun α ↦ Sheaf.hom_ext (Functor.IsCoverDense.sheafHom_restrict_eq α.hom)
      preimage_map := fun α ↦ Sheaf.hom_ext (Functor.IsCoverDense.sheafHom_eq (etaleBaseChange i) α.hom) }

/-- Compose actual chart extension with the explicit gluing inverse on Hom sets. -/
def directImageFullyFaithful : (EtaleAdditive.directImage i).FullyFaithful :=
  (EtaleAdditive.siteEquivalence X).fullyFaithfulInverse.comp (restrictionFullyFaithful i)

/-- The thickening counit and its actual inverse from sheaf gluing. -/
def counitIso (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u}) :
    (EtaleAdditive.inverseImage i).obj ((EtaleAdditive.directImage i).obj F) ≅ F where
  hom := (EtaleAdditive.adjunction i).counit.app F
  inv := (directImageFullyFaithful i).preimage
    ((EtaleAdditive.adjunction i).unit.app ((EtaleAdditive.directImage i).obj F))
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward map is exactly the original geometric counit. -/
theorem counitIso_hom (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u}) :
    (counitIso i F).hom = (EtaleAdditive.adjunction i).counit.app F := rfl

/-- The inverse is the gluing reconstruction of the actual geometric unit. -/
theorem counitIso_inv (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u}) :
    (counitIso i F).inv = (directImageFullyFaithful i).preimage
      ((EtaleAdditive.adjunction i).unit.app ((EtaleAdditive.directImage i).obj F)) := rfl

end AlgebraicGeometry.AlgebraicSpace.EtaleAdditive.Thickening
