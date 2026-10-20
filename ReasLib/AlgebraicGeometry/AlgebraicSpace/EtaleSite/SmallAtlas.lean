module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Atlas.Input
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Presentation
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.InducedCategory
public import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology

/-! # An explicit small affine-étale atlas site below module pullback

Charts use actual scheme arrows and the supplied atlas map. No module
restriction, selected inverse image, or meromorphic owner is imported.
-/

@[expose] public section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace.PullbackFactory.SmallAtlas

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
    (U : Over S) (a : ofOver U ⟶ X) [AlgebraicSpace.Etale a]

def schemeObject (W : U.left.Etale) : Over S := Over.mk (W.hom ≫ U.hom)

def schemeArrow (W : U.left.Etale) : schemeObject U W ⟶ U :=
  Over.homMk W.hom rfl

/-- The actual chart composite is étale; no new chart data are selected. -/
theorem chart_etale (W : U.left.Etale) :
    AlgebraicSpace.Etale ((ofOverFunctor S).map (schemeArrow U W) ≫ a) := by
  sorry

def chart (W : U.left.Etale) : smallEtaleSite X :=
  smallEtaleSite.mk ((ofOverFunctor S).map (schemeArrow U W) ≫ a) (chart_etale U a W)

def schemeArrowMap {W W' : U.left.Etale} (f : W ⟶ W') :
    schemeObject U W ⟶ schemeObject U W' :=
  Over.homMk f.left (by sorry)

def etaleCharts : U.left.Etale ⥤ smallEtaleSite X where
  obj := chart U a
  map f := MorphismProperty.CostructuredArrow.homMk (schemeArrowMap U f) trivial (by sorry)
  map_id _ := by apply MorphismProperty.CostructuredArrow.Hom.ext; rfl
  map_comp _ _ := by apply MorphismProperty.CostructuredArrow.Hom.ext; rfl

def charts : U.left.AffineEtale ⥤ smallEtaleSite X :=
  Scheme.AffineEtale.Spec U.left ⋙ etaleCharts U a

theorem charts_essentiallySmall : EssentiallySmall.{u} U.left.AffineEtale := by infer_instance

def Index : Type u := @SmallModel.{u} U.left.AffineEtale _ (charts_essentiallySmall U)

def object (i : Index U) : smallEtaleSite X :=
  (charts U a).obj ((equivSmallModel U.left.AffineEtale).inverse.obj i)

abbrev Site := InducedCategory (smallEtaleSite X) (object U a)
def inclusion : Site U a ⥤ smallEtaleSite X := inducedFunctor (object U a)

instance inclusion_full : (inclusion U a).Full := InducedCategory.full _
instance inclusion_faithful : (inclusion U a).Faithful := InducedCategory.faithful _

def topology : GrothendieckTopology (Site U a) :=
  (inclusion U a).inducedTopology (smallEtaleTopology X)

theorem inclusion_coverDense
    (ha : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) a) :
    (inclusion U a).IsCoverDense (smallEtaleTopology X) := by
  sorry

theorem denseSubsite
    (ha : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) a) :
    (inclusion U a).IsDenseSubsite (topology U a) (smallEtaleTopology X) := by
  -- Local instance justification (proof-local temporary data): Use the cover-density proved for the supplied etale atlas a to obtain the induced-topology dense-subsite law.
  letI := inclusion_coverDense U a ha
  change (inclusion U a).IsDenseSubsite
    ((inclusion U a).inducedTopology (smallEtaleTopology X)) (smallEtaleTopology X)
  infer_instance

end AlgebraicGeometry.AlgebraicSpace.PullbackFactory.SmallAtlas

namespace AlgebraicGeometry.AlgebraicSpace.AtlasInput

variable {S : Scheme.{u}} (X : AlgebraicSpace S)

/-- Input representable étaleness is the required actual chart property. -/
instance etale : AlgebraicSpace.Etale (map X) where
  of_etale φ hφ := by
    -- Local instance justification (proof-local temporary data): Lift etale composition stability to Over S inside the atlas covering proof, with the component morphisms unchanged.
    letI : (MorphismProperty.over (@AlgebraicGeometry.Etale) :
        MorphismProperty (Over S)).IsStableUnderComposition :=
      { comp_mem := fun {A B C} f g hf hg ↦ by
          -- Local instance justification (proof-local temporary data): Expose the supplied etale certificate hf for the first underlying scheme map in this composition proof.
          letI : AlgebraicGeometry.Etale f.left := hf
          -- Local instance justification (proof-local temporary data): Expose the supplied etale certificate hg for the second underlying scheme map in this composition proof.
          letI : AlgebraicGeometry.Etale g.left := hg
          change AlgebraicGeometry.Etale (f.left ≫ g.left)
          infer_instance }
    exact (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf.comp_mem
      φ (map X) hφ (representableEtale X)

end AlgebraicGeometry.AlgebraicSpace.AtlasInput
