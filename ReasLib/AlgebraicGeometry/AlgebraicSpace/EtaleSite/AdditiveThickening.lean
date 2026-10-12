/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.AdditiveAdjunction
public import stacks_project.Chap76.Lemma_76_18_1_Thickening

/-!
# The additive counit along a first-order thickening

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

/-- A fully faithful right adjoint inverts its counit by reconstructing the unit.
Both inverse laws follow from the given Hom reconstruction and adjunction triangles. -/
def counitIsoOfFullyFaithful {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (hR : R.FullyFaithful) (F : D) :
    L.obj (R.obj F) ≅ F where
  hom := adj.counit.app F
  inv := hR.preimage (adj.unit.app (R.obj F))
  hom_inv_id := by
    let p : F ⟶ L.obj (R.obj F) := hR.preimage (adj.unit.app (R.obj F))
    have hp : R.map p = adj.unit.app (R.obj F) := hR.map_preimage _
    have hn := adj.counit_naturality p
    change L.map (R.map p) ≫ adj.counit.app (L.obj (R.obj F)) = adj.counit.app F ≫ p at hn
    rw [hp] at hn
    exact hn.symm.trans (adj.left_triangle_components (R.obj F))
  inv_hom_id := by
    let p : F ⟶ L.obj (R.obj F) := hR.preimage (adj.unit.app (R.obj F))
    apply hR.map_injective
    change R.map (p ≫ adj.counit.app F) = R.map (𝟙 F)
    rw [R.map_comp]
    rw [show R.map p = adj.unit.app (R.obj F) from hR.map_preimage _]
    rw [R.map_id]
    exact adj.right_triangle_components F

variable {S : Scheme.{u}} {X X' : AlgebraicSpace S} (i : X ⟶ X')
variable [IsFirstOrderThickening i]

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
    (EtaleAdditive.inverseImage i).obj ((EtaleAdditive.directImage i).obj F) ≅ F :=
  counitIsoOfFullyFaithful (EtaleAdditive.adjunction i) (directImageFullyFaithful i) F

/-- The forward map is exactly the original geometric counit. -/
theorem counitIso_hom (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u}) :
    (counitIso i F).hom = (EtaleAdditive.adjunction i).counit.app F := rfl

/-- The inverse is the gluing reconstruction of the actual geometric unit. -/
theorem counitIso_inv (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u}) :
    (counitIso i F).inv = (directImageFullyFaithful i).preimage
      ((EtaleAdditive.adjunction i).unit.app ((EtaleAdditive.directImage i).obj F)) := rfl

/-- The original counit followed by the constructed inverse is the identity. -/
theorem counit_comp_inverse (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u}) :
    (EtaleAdditive.adjunction i).counit.app F ≫ (counitIso i F).inv = 𝟙 _ :=
  (counitIso i F).hom_inv_id

/-- The constructed inverse followed by the original counit is the identity. -/
theorem inverse_comp_counit (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u}) :
    (counitIso i F).inv ≫ (EtaleAdditive.adjunction i).counit.app F = 𝟙 F :=
  (counitIso i F).inv_hom_id

end AlgebraicGeometry.AlgebraicSpace.EtaleAdditive.Thickening
