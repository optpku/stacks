/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect
public import Mathlib.AlgebraicGeometry.Cover.Open
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ComplexChart.GraphProducer

/-!
# A global model atlas extracted from original perfectness

The data below are selected only from the defining local-presentation input
`hE : IsPerfect E`. No admitted existence of charts or modifications is used.
The output is a cover with actual strictly-perfect models, quasi-isomorphisms,
and finite-free retractions of their terms. Affine divisor coordinates and
gluing the graph modifications are later, distinct construction steps.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.PerfectGraphAtlas

variable {X : Scheme.{u}} (E : RingedSpace.ModuleDerived X.toRingedSpace)
  (hE : RingedSpace.ModuleDerived.IsPerfect E)

/-- The complex representative already supplied by the defining perfectness input. -/
def representative : CochainComplex X.toRingedSpace.Modules ℤ :=
  Classical.choose hE

/-- The given derived object is identified with that chosen input representative. -/
def representationIso : E ≅ DerivedCategory.Q.obj (representative E hE) :=
  Classical.choose (Classical.choose_spec hE)

/-- The representative is perfect by the original witness, without an existence bridge. -/
theorem representative_perfect :
    RingedSpace.CochainComplex.IsPerfect (representative E hE) :=
  Classical.choose_spec (Classical.choose_spec hE)

/-- The covering sieve occurring in the definition of perfectness, evaluated on the whole space. -/
def modelSieve : (Opens.grothendieckTopology X).Cover (⊤ : X.Opens) :=
  Classical.choose (representative_perfect E hE ⊤)

/-- Each arrow in the input covering sieve has its input strictly-perfect model. -/
theorem model_exists (i : (modelSieve E hE).Arrow) :
    SheafOfModules.CochainComplex.hasStrictlyPerfectModel
      ((SheafOfModules.CochainComplex.localizedRestrictionComplex
        (R := X.toRingedSpace.ringCatSheaf) i.Y).obj (representative E hE)) :=
  Classical.choose_spec (representative_perfect E hE ⊤) i

/-- The local complex is selected from the original local-presentation input. -/
def model (i : (modelSieve E hE).Arrow) :=
  Classical.choose (model_exists E hE i)

/-- The actual quasi-isomorphism from the local model to the restricted input representative. -/
def modelMap (i : (modelSieve E hE).Arrow) :
    model E hE i ⟶
      (SheafOfModules.CochainComplex.localizedRestrictionComplex
        (R := X.toRingedSpace.ringCatSheaf) i.Y).obj (representative E hE) :=
  Classical.choose (Classical.choose_spec (model_exists E hE i))

/-- Strict perfectness of the selected local model is part of the original input. -/
theorem model_strictlyPerfect (i : (modelSieve E hE).Arrow) :
    SheafOfModules.CochainComplex.IsStrictlyPerfect (model E hE i) :=
  (Classical.choose_spec (Classical.choose_spec (model_exists E hE i))).1

/-- The selected comparison is a quasi-isomorphism by the original input proof. -/
theorem modelMap_quasiIso (i : (modelSieve E hE).Arrow) :
    letI := SheafOfModules.CochainComplex.moduleCategoryWithHomology
      (X.toRingedSpace.ringCatSheaf.over i.Y)
    QuasiIso (modelMap E hE i) :=
  (Classical.choose_spec (Classical.choose_spec (model_exists E hE i))).2

/-- The chosen local model is bounded, directly by its defining conjunction. -/
theorem model_bounded (i : (modelSieve E hE).Arrow) :
    CochainComplex.bounded _ (model E hE i) :=
  (model_strictlyPerfect E hE i).1

/-- The finite-free ambient module appearing in the input retract condition of a local term. -/
def termAmbient (i : (modelSieve E hE).Arrow) (n : ℤ) :=
  Classical.choose ((model_strictlyPerfect E hE i).2 n)

/-- The selected ambient is finite free by the input's own certificate. -/
theorem termAmbient_finiteFree (i : (modelSieve E hE).Arrow) (n : ℤ) :
    SheafOfModules.IsFiniteFree (termAmbient E hE i n) :=
  Classical.choose (Classical.choose_spec ((model_strictlyPerfect E hE i).2 n))

/-- The splitting maps already supplied by termwise finite-free retractness. -/
def termRetraction (i : (modelSieve E hE).Arrow) (n : ℤ) :
    Retract ((model E hE i).X n) (termAmbient E hE i n) :=
  Classical.choice (Classical.choose_spec
    (Classical.choose_spec ((model_strictlyPerfect E hE i).2 n)))

/-- The finite generator index from the selected input finite-free module. -/
def generatorIndex (i : (modelSieve E hE).Arrow) (n : ℤ) : Type u :=
  Classical.choose (termAmbient_finiteFree E hE i n).exists_iso_free

/-- Finiteness of the generator index comes directly from the original presentation. -/
theorem generatorIndex_finite (i : (modelSieve E hE).Arrow) (n : ℤ) :
    Finite (generatorIndex E hE i n) :=
  (Classical.choose_spec (termAmbient_finiteFree E hE i n).exists_iso_free).1

/-- The actual input identification of the ambient module with its finite free module. -/
def termAmbientIso (i : (modelSieve E hE).Arrow) (n : ℤ) :
    termAmbient E hE i n ≅ SheafOfModules.free (generatorIndex E hE i n) :=
  Classical.choice (Classical.choose_spec (termAmbient_finiteFree E hE i n).exists_iso_free).2

/-- The original term is a retract of the specified standard finite free sheaf. -/
def finiteFreeRetraction (i : (modelSieve E hE).Arrow) (n : ℤ) :
    Retract ((model E hE i).X n) (SheafOfModules.free (generatorIndex E hE i n)) :=
  (termRetraction E hE i n).trans (Retract.ofIso (termAmbientIso E hE i n))

/-- The local model term is recovered by the actual inclusion followed by its actual retraction. -/
theorem finiteFreeRetraction_split (i : (modelSieve E hE).Arrow) (n : ℤ) :
    (finiteFreeRetraction E hE i n).i ≫ (finiteFreeRetraction E hE i n).r = 𝟙 _ :=
  (finiteFreeRetraction E hE i n).retract

/-- The actual idempotent on a standard finite free sheaf that presents the local term. -/
def termProjector (i : (modelSieve E hE).Arrow) (n : ℤ) :
    (SheafOfModules.free (R := X.toRingedSpace.ringCatSheaf.over i.Y) (generatorIndex E hE i n)) ⟶
      SheafOfModules.free (R := X.toRingedSpace.ringCatSheaf.over i.Y) (generatorIndex E hE i n) :=
  (finiteFreeRetraction E hE i n).r ≫ (finiteFreeRetraction E hE i n).i

/-- The constructed endomorphism is idempotent by the input splitting equation. -/
theorem termProjector_idempotent (i : (modelSieve E hE).Arrow) (n : ℤ) :
    termProjector E hE i n ≫ termProjector E hE i n = termProjector E hE i n := by
  simp [termProjector, Category.assoc]

/-- Every point belongs to an actual member of the input model sieve. -/
theorem modelSieve_covers (x : X) : ∃ i : (modelSieve E hE).Arrow, x ∈ i.Y := by
  obtain ⟨U, f, hf, hx⟩ := (modelSieve E hE).condition x (by trivial)
  exact ⟨⟨U, f, hf⟩, hx⟩

/-- The actual scheme open cover, with no caller-supplied coordinate chart. -/
def openCover : X.OpenCover :=
  Scheme.Cover.mkOfCovers ((modelSieve E hE).Arrow)
    (fun i => Scheme.Opens.toScheme (X := X) i.Y) (fun i => Scheme.Opens.ι (X := X) i.Y)
    (by
      intro x
      obtain ⟨i, hi⟩ := modelSieve_covers E hE x
      exact ⟨i, ⟨x, hi⟩, rfl⟩)

/-- The open-cover member is the actual open in the input sieve. -/
theorem openCover_obj (i : (modelSieve E hE).Arrow) :
    (openCover E hE).X i = Scheme.Opens.toScheme (X := X) i.Y := rfl

/-- The open-cover map is the ordinary open immersion. -/
theorem openCover_map (i : (modelSieve E hE).Arrow) :
    (openCover E hE).f i = Scheme.Opens.ι (X := X) i.Y := rfl

variable {Y : Scheme.{u}} (p : Y ⟶ X)

/-- The original model cover pulled back along the specified map `p`. -/
def pullbackCover : Y.OpenCover :=
  Scheme.Cover.mkOfCovers ((modelSieve E hE).Arrow)
    (fun i => (p ⁻¹ᵁ i.Y : Y.Opens).toScheme) (fun i => (p ⁻¹ᵁ i.Y : Y.Opens).ι)
    (by
      intro y
      obtain ⟨i, hi⟩ := modelSieve_covers E hE (p y)
      exact ⟨i, ⟨y, hi⟩, rfl⟩)

/-- The pullback cover uses precisely the inverse-image open and its inclusion. -/
theorem pullbackCover_map (i : (modelSieve E hE).Arrow) :
    (pullbackCover E hE p).f i = (p ⁻¹ᵁ i.Y : Y.Opens).ι := rfl

/-- The specified map on one pulled-back open cover member. -/
def pullbackMap (i : (modelSieve E hE).Arrow) :
    (pullbackCover E hE p).X i ⟶ (openCover E hE).X i :=
  p.resLE i.Y (p ⁻¹ᵁ i.Y) le_rfl

/-- The actual restriction map commutes with the maps to the original base. -/
theorem pullbackMap_over (i : (modelSieve E hE).Arrow) :
    pullbackMap E hE p i ≫ (openCover E hE).f i =
      (pullbackCover E hE p).f i ≫ p := by
  exact Scheme.Hom.resLE_comp_ι _ _

end AlgebraicGeometry.Scheme.PerfectGraphAtlas
