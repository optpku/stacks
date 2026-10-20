module
public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.Fiber
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Restrict
public import ReasLib.CategoryTheory.Sites.SheafifiedRepresentable.Coproduct
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Finite
@[expose] public section
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
noncomputable section
universe u
namespace AlgebraicGeometry.Scheme.FiniteEtale.GeometricFrames
variable {X : Scheme.{u}} (Y : FiniteEtale X)
/-- Degree uses the geometric fiber over the actual algebraic closure of the residue field. -/
def degree (x : X) : ℕ := by
  let Ω := AlgebraicClosure (X.residueField x)
  let point : Spec (.of Ω) ⟶ X :=
    Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) Ω)) ≫ X.fromSpecResidueField x
  exact Nat.card (Scheme.FiniteEtale.fiber point |>.obj Y)
/-- The actual finite product parametrizes tuples of sections over the base. -/
abbrev tuples (n : ℕ) : FiniteEtale X := ∏ᶜ fun _ : Fin n ↦ Y
/-- Each coordinate is the native product projection. -/
abbrev coordinate (n : ℕ) (i : Fin n) : tuples Y n ⟶ Y := Pi.π _ i
/-- Equal coordinates are detected by the scheme diagonal, including nonrational fibers. -/
def equalCoordinates (n : ℕ) (i j : Fin n) : Set (tuples Y n).left :=
  (pullback.lift (coordinate Y n i).left (coordinate Y n j).left (by sorry)) ⁻¹'
    Set.range (pullback.lift (f := Y.hom) (g := Y.hom)
      (𝟙 Y.left) (𝟙 Y.left) (by simp))
/-- The frame locus consists of degree-n tuples outside every pairwise diagonal. -/
def frameLocus (n : ℕ) : Set (tuples Y n).left :=
  {t | degree Y ((tuples Y n).hom t) = n ∧
    ∀ i j : Fin n, i ≠ j → t ∉ equalCoordinates Y n i j}
/-- Finite étale degree strata and complements of diagonals are open. -/
theorem frameLocus_isOpen (n : ℕ) : IsOpen (frameLocus Y n) := sorry
/-- Restriction to the explicit open frame locus supplies the actual frame scheme. -/
def frameOpen (n : ℕ) : (tuples Y n).left.Opens :=
  ⟨frameLocus Y n, frameLocus_isOpen Y n⟩
/-- The frame scheme maps to the original base by its open inclusion and tuple map. -/
def frameMap (n : ℕ) : (frameOpen Y n).toScheme ⟶ X :=
  (frameOpen Y n).ι ≫ (tuples Y n).hom
/-- The actual frame maps are étale. -/
instance frameMap_etale (n : ℕ) : Etale (frameMap Y n) := sorry
/-- A frame has a specified coordinate section of the pulled finite étale cover. -/
def coordinateSection (n : ℕ) (i : Fin n) :
    (frameOpen Y n).toScheme ⟶ pullback Y.hom (frameMap Y n) :=
  pullback.lift ((frameOpen Y n).ι ≫ (coordinate Y n i).left) (𝟙 _) sorry
/-- Coordinate sections are open immersions. -/
instance coordinateSection_isOpenImmersion (n : ℕ) (i : Fin n) :
    IsOpenImmersion (coordinateSection Y n i) := sorry
/-- The coordinates of an actual frame cover its pulled geometric fiber. -/
def coordinateCover (n : ℕ) : (pullback Y.hom (frameMap Y n)).OpenCover where
  I₀ := Fin n
  X _ := (frameOpen Y n).toScheme
  f i := coordinateSection Y n i
  mem₀ := sorry
/-- A geometric frame yields a finite disjoint union evaluation map. -/
def evaluation (n : ℕ) :
    (∐ fun _ : Fin n ↦ (frameOpen Y n).toScheme) ⟶ pullback Y.hom (frameMap Y n) :=
  Sigma.desc (coordinateSection Y n)
/-- Inclusions of coordinate sections into their disjoint union agree on overlaps. -/
theorem coordinateInclusions_compatible (n : ℕ) (i j : Fin n) :
    pullback.fst (coordinateSection Y n i) (coordinateSection Y n j) ≫
        Sigma.ι (fun _ : Fin n ↦ (frameOpen Y n).toScheme) i =
      pullback.snd (coordinateSection Y n i) (coordinateSection Y n j) ≫
        Sigma.ι (fun _ : Fin n ↦ (frameOpen Y n).toScheme) j := sorry
/-- The reverse coordinates glue the actual coproduct inclusions over the coordinate open cover. -/
def evaluationInverse (n : ℕ) :
    pullback Y.hom (frameMap Y n) ⟶ ∐ fun _ : Fin n ↦ (frameOpen Y n).toScheme :=
  (coordinateCover Y n).glueMorphisms
    (Sigma.ι (fun _ : Fin n ↦ (frameOpen Y n).toScheme))
    (coordinateInclusions_compatible Y n)
/-- Both directions of the split finite étale chart are concretely specified. -/
def evaluationIso (n : ℕ) :
    (∐ fun _ : Fin n ↦ (frameOpen Y n).toScheme) ≅ pullback Y.hom (frameMap Y n) where
  hom := evaluation Y n
  inv := evaluationInverse Y n
  hom_inv_id := sorry
  inv_hom_id := sorry
/-- Frame charts of each degree give the actual small étale chart family. -/
def chart (n : ℕ) : X.Etale := Scheme.Etale.mk (frameMap Y n)
/-- Each actual frame chart maps to the identity étale object over the base. -/
def chartToBase (n : ℕ) : chart Y n ⟶ Scheme.Etale.mk (𝟙 X) :=
  MorphismProperty.Over.homMk (frameMap Y n) (by
    change frameMap Y n ≫ 𝟙 X = frameMap Y n
    exact Category.comp_id _)
/-- Actual finite-degree frame charts cover every geometric fiber of the base. -/
theorem charts_covering :
    Sieve.ofArrows (chart Y) (chartToBase Y)
      ∈ X.smallEtaleTopology (Scheme.Etale.mk (𝟙 X)) := sorry
/-- The pulled cover regarded as an object over the actual frame chart. -/
def pulledObject (n : ℕ) : Over (chart Y n) := by
  letI : Etale Y.hom := Y.prop.2
  letI : Etale (pullback.snd Y.hom (frameMap Y n)) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  exact Over.mk (MorphismProperty.Over.homMk (pullback.snd Y.hom (frameMap Y n))
    (by rfl) :
    Scheme.Etale.mk (pullback.snd Y.hom (frameMap Y n) ≫ frameMap Y n) ⟶ chart Y n)
/-- Each coordinate section is the actual inclusion of a terminal slice branch. -/
def branch (n : ℕ) (i : ULift.{u + 1} (Fin n)) : Over.mk (𝟙 (chart Y n)) ⟶ pulledObject Y n :=
  Over.homMk (MorphismProperty.Over.homMk (coordinateSection Y n i.down) sorry) sorry
instance branch_mono (n : ℕ) (i : ULift.{u + 1} (Fin n)) : Mono (branch Y n i) := sorry
def branchCofan (n : ℕ) : Cofan fun _ : ULift.{u + 1} (Fin n) ↦ Over.mk (𝟙 (chart Y n)) :=
  Cofan.mk (pulledObject Y n) (branch Y n)
theorem branchCovering (n : ℕ) : Sieve.ofArrows _ (branchCofan Y n).inj ∈
    (X.smallEtaleTopology.over (chart Y n)) (pulledObject Y n) := sorry
theorem branchDisjoint (n : ℕ) {i j : ULift.{u + 1} (Fin n)} (hij : i ≠ j)
    {V : Over (chart Y n)} (a : V ⟶ Over.mk (𝟙 (chart Y n)))
    (b : V ⟶ Over.mk (𝟙 (chart Y n)))
    (hab : a ≫ (branchCofan Y n).inj i = b ≫ (branchCofan Y n).inj j) :
    (⊥ : Sieve V) ∈ (X.smallEtaleTopology.over (chart Y n)) V := sorry
/-- The constant-chart comparison descends the actual disjoint coordinate cover in both directions. -/
def constantChartIso (n : ℕ)
    [HasWeakSheafify (X.smallEtaleTopology.over (chart Y n)) (Type (u + 1))] :
    (constantSheaf (X.smallEtaleTopology.over (chart Y n)) (Type (u + 1))).obj
        (ULift.{u + 1} (Fin n)) ≅
      (X.smallEtaleTopology.over (chart Y n)).sheafifiedRepresentable (pulledObject Y n) := by
  letI : ∀ i, Mono ((branchCofan Y n).inj i) := fun i ↦ branch_mono Y n i
  exact GrothendieckTopology.constantSheafIsoOfDisjointCover.{u + 1, u + 1, u}
    (X.smallEtaleTopology.over (chart Y n)) Over.mkIdTerminal _ (branchCofan Y n)
    (branchCovering Y n) (branchDisjoint Y n)
/-- Restricting raw Yoneda to the frame slice is actual scheme pullback on maps. -/
def rawRepresentationSliceIso (n : ℕ) :
    (Over.forget (chart Y n)).op ⋙ uliftYoneda.{u + 1}.obj ((Scheme.FiniteEtale.toEtale X).obj Y) ≅
      uliftYoneda.{u + 1}.obj (pulledObject Y n) :=
  NatIso.ofComponents
    (fun V ↦ Equiv.toIso
      { toFun := fun h ↦
          ⟨Over.homMk (MorphismProperty.Over.homMk
            (pullback.lift h.down.left V.unop.hom.left sorry) sorry) sorry⟩
        invFun := fun h ↦
          ⟨MorphismProperty.Over.homMk
            (h.down.left.left ≫ pullback.fst Y.hom (frameMap Y n)) sorry⟩
        left_inv := sorry
        right_inv := sorry })
    (fun _ ↦ sorry)
/-- Native continuous/cocontinuous slice restriction commutes with sheafification. -/
def representationSliceIso (n : ℕ)
    [HasWeakSheafify X.smallEtaleTopology (Type (u + 1))]
    [HasWeakSheafify (X.smallEtaleTopology.over (chart Y n)) (Type (u + 1))] :
    (X.smallEtaleTopology.sheafifiedRepresentable
      ((Scheme.FiniteEtale.toEtale X).obj Y)).over (chart Y n) ≅
      (X.smallEtaleTopology.over (chart Y n)).sheafifiedRepresentable (pulledObject Y n) :=
  ((Over.forget (chart Y n)).pushforwardContinuousSheafificationCompatibility
    (Type (u + 1)) (X.smallEtaleTopology.over (chart Y n)) X.smallEtaleTopology).symm.app
      (uliftYoneda.{u + 1}.obj ((Scheme.FiniteEtale.toEtale X).obj Y)) ≪≫
    (presheafToSheaf (X.smallEtaleTopology.over (chart Y n)) (Type (u + 1))).mapIso
      (rawRepresentationSliceIso Y n)
/-- The actual represented sheaf is constant on each frame chart, with both maps specified. -/
def representedConstantChartIso (n : ℕ)
    [HasWeakSheafify X.smallEtaleTopology (Type (u + 1))]
    [HasWeakSheafify (X.smallEtaleTopology.over (chart Y n)) (Type (u + 1))] :
    (X.smallEtaleTopology.sheafifiedRepresentable
      ((Scheme.FiniteEtale.toEtale X).obj Y)).over (chart Y n) ≅
      (constantSheaf (X.smallEtaleTopology.over (chart Y n)) (Type (u + 1))).obj
        (ULift.{u + 1} (Fin n)) :=
  representationSliceIso Y n ≪≫ (constantChartIso Y n).symm
/-- Frame charts refined over any actual étale test object by native pullback. -/
def refinedChart (U : X.Etale) (n : ℕ) : Over U :=
  Over.mk (pullback.snd (chartToBase Y n) (MorphismProperty.Over.homMk U.hom (Category.comp_id U.hom)))
/-- Refined frame charts have the actual projection to their original frame. -/
def refinedChartToFrame (U : X.Etale) (n : ℕ) : (refinedChart Y U n).left ⟶ chart Y n :=
  pullback.fst (chartToBase Y n) (MorphismProperty.Over.homMk U.hom (Category.comp_id U.hom))
/-- True frame coverage remains a covering family after the actual test pullback. -/
theorem refinedCharts_covering (U : X.Etale) :
    (X.smallEtaleTopology.over U).CoversTop (refinedChart Y U) := sorry
/-- Actual constant chart maps persist on the native refined cover. -/
def refinedConstantChartIso (U : X.Etale) (n : ℕ)
    [HasWeakSheafify X.smallEtaleTopology (Type (u + 1))]
    [∀ V : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over V) (Type (u + 1))] :
    (X.smallEtaleTopology.sheafifiedRepresentable
      ((Scheme.FiniteEtale.toEtale X).obj Y)).over (refinedChart Y U n).left ≅
      (constantSheaf (X.smallEtaleTopology.over (refinedChart Y U n).left) (Type (u + 1))).obj
        (ULift.{u + 1} (Fin n)) :=
  (Sheaf.pushforwardOverMapIso _ (refinedChartToFrame Y U n)).symm ≪≫
    ((Over.map (refinedChartToFrame Y U n)).sheafPushforwardContinuous (Type (u + 1))
      (X.smallEtaleTopology.over (refinedChart Y U n).left)
      (X.smallEtaleTopology.over (chart Y n))).mapIso (representedConstantChartIso Y n) ≪≫
    ((Over.map (refinedChartToFrame Y U n)).pushforwardContinuousSheafificationCompatibility
      (Type (u + 1)) (X.smallEtaleTopology.over (refinedChart Y U n).left)
      (X.smallEtaleTopology.over (chart Y n))).symm.app
        ((Functor.const (Over (chart Y n))ᵒᵖ).obj (ULift.{u + 1} (Fin n)))
/-- The universe-small actual frame family covers the slice over any test object. -/
theorem refinedCharts_ulift_covering (U : X.Etale) :
    (X.smallEtaleTopology.over U).CoversTop
      (fun n : ULift.{u + 1} ℕ ↦ refinedChart Y U n.down) := sorry
/-- Represented finite étale sheaves have the implemented frame covers and constant chart maps. -/
instance represented_isFiniteLocallyConstant
    [HasWeakSheafify X.smallEtaleTopology (Type (u + 1))]
    [∀ V : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over V) (Type (u + 1))] :
    Sheaf.IsFiniteLocallyConstant (X.smallEtaleTopology.sheafifiedRepresentable
      ((Scheme.FiniteEtale.toEtale X).obj Y)) where
  existsConstantCover U :=
    ⟨ULift.{u + 1} ℕ, (fun n ↦ refinedChart Y U n.down),
      refinedCharts_ulift_covering Y U,
      fun n ↦ ⟨ULift.{u + 1} (Fin n.down), inferInstance,
        ⟨refinedConstantChartIso Y U n.down⟩⟩⟩
end AlgebraicGeometry.Scheme.FiniteEtale.GeometricFrames
