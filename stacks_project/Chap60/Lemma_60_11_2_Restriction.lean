/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap60.Definition_60_11_1_ModuleProperties
public import stacks_project.Chap60.Definition_60_8_4
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.InducedTopology

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Crystalline
open SheafOfModules
open CrystallineModuleSheaf

universe u

@[expose] public section

variable {S : Scheme.{u}} {I : S.IdealSheafData}
variable {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
variable {h_compatible :
    ∀ (V : S.affineOpens) (f : Γ(S, V)),
      (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
        (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
variable {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}

/-- The Grothendieck topology on `Cris(X/S)` induced from the big crystalline Zariski
topology. -/
def smallCrystallineZariskiTopology :
    GrothendieckTopology (smallCrystallineSite S I γ h_compatible X x₀) :=
  (smallCrystallineProperty S I γ h_compatible X x₀).ι.inducedTopology
    (crystallineZariskiTopology S I γ h_compatible X x₀)

/-- The induced small crystalline topology is the induced topology of the big
crystalline Zariski topology along the inclusion of `Cris(X/S)`. -/
theorem smallCrystallineZariskiTopology_def :
    smallCrystallineZariskiTopology (S := S) (I := I) (γ := γ)
        (h_compatible := h_compatible) (X := X) (x₀ := x₀) =
      (smallCrystallineProperty S I γ h_compatible X x₀).ι.inducedTopology
        (crystallineZariskiTopology S I γ h_compatible X x₀) :=
  rfl

/-- Every crystalline thickening appearing in Definition 60.11.1 is compatible with the
base divided-power setup, so it determines an object of `RelativeCRIS(X/S)`. -/
theorem relativeCRIS_of_CRIS (A : CRIS S I γ h_compatible X x₀) :
    CrystallineBaseCompatible I γ h_compatible x₀ A := sorry

/-- The relative crystalline object associated to a crystalline thickening. -/
def toRelativeCRIS (A : CRIS S I γ h_compatible X x₀) :
    RelativeCRIS S I γ h_compatible X x₀ :=
  ⟨A, relativeCRIS_of_CRIS A⟩

/-- The slice of a crystalline sheaf of modules over a thickening is a module sheaf on
that thickening. -/
theorem sliceModules_eq
    {𝒪 : Sheaf (crystallineZariskiTopology S I γ h_compatible X x₀) RingCat.{u}}
    (A : CRIS S I γ h_compatible X x₀) :
    SheafOfModules (𝒪.over (toRelativeCRIS A)) = A.thickening.Modules := sorry

/-- Objectwise restriction of a sheaf of modules on `CRIS(X/S)` to the thickening of a
crystalline object. -/
noncomputable def CrystallineModuleSheaf.restrictObj
    {𝒪 : Sheaf (crystallineZariskiTopology S I γ h_compatible X x₀) RingCat.{u}}
    (F : SheafOfModules 𝒪) (A : CRIS S I γ h_compatible X x₀) :
    A.thickening.Modules :=
  Eq.mp (sliceModules_eq (𝒪 := 𝒪) A) (F.over (toRelativeCRIS A))

/-- Pullback of the restricted module sheaf along a thickening morphism recovers the
restricted module sheaf of the source. -/
theorem restrictObj_pullback
    {𝒪 : Sheaf (crystallineZariskiTopology S I γ h_compatible X x₀) RingCat.{u}}
    (F : SheafOfModules 𝒪) {A B : CRIS S I γ h_compatible X x₀}
    (f : CrystallineObject.Hom A B) :
    (Scheme.Modules.pullback f.thickening).obj
      (CrystallineModuleSheaf.restrictObj F B) =
      CrystallineModuleSheaf.restrictObj F A := sorry

/-- Comparison of restricted module sheaves along a morphism of crystalline objects. -/
noncomputable def CrystallineModuleSheaf.restrictComparison
    {𝒪 : Sheaf (crystallineZariskiTopology S I γ h_compatible X x₀) RingCat.{u}}
    (F : SheafOfModules 𝒪) {A B : CRIS S I γ h_compatible X x₀}
    (f : CrystallineObject.Hom A B) :
    (Scheme.Modules.pullback f.thickening).obj
      (CrystallineModuleSheaf.restrictObj F B) ⟶
      CrystallineModuleSheaf.restrictObj F A :=
  eqToHom (restrictObj_pullback (𝒪 := 𝒪) F f)

/-- Canonical restriction of a site-level module sheaf on `CRIS(X/S)` to crystalline
module-sheaf data on thickenings. -/
noncomputable def CrystallineModuleSheaf.restrict
    {𝒪 : Sheaf (crystallineZariskiTopology S I γ h_compatible X x₀) RingCat.{u}}
    (F : SheafOfModules 𝒪) :
    CrystallineModuleSheaf S I γ h_compatible X x₀ :=
  CrystallineModuleSheaf.of I γ h_compatible X x₀
    (fun A ↦ CrystallineModuleSheaf.restrictObj F A)
    (fun f ↦ CrystallineModuleSheaf.restrictComparison F f)

/-- Objectwise, `restrict F` is the thickening restriction of `F`. -/
theorem CrystallineModuleSheaf.restrict_obj
    {𝒪 : Sheaf (crystallineZariskiTopology S I γ h_compatible X x₀) RingCat.{u}}
    (F : SheafOfModules 𝒪) (A : CRIS S I γ h_compatible X x₀) :
    (CrystallineModuleSheaf.restrict F).obj A =
      CrystallineModuleSheaf.restrictObj F A :=
  rfl

/-- The comparison map of `restrict F` is the thickening-pullback comparison of `F`. -/
theorem CrystallineModuleSheaf.restrict_comparison
    {𝒪 : Sheaf (crystallineZariskiTopology S I γ h_compatible X x₀) RingCat.{u}}
    (F : SheafOfModules 𝒪) {A B : CRIS S I γ h_compatible X x₀}
    (f : CrystallineObject.Hom A B) :
    (CrystallineModuleSheaf.restrict F).comparison f =
      CrystallineModuleSheaf.restrictComparison F f :=
  rfl

/-- The slice of a small-site sheaf of modules over a small crystalline object is a
module sheaf on its thickening. -/
theorem crisSliceModules_eq
    {𝒪 : Sheaf (smallCrystallineZariskiTopology (S := S) (I := I) (γ := γ)
      (h_compatible := h_compatible) (X := X) (x₀ := x₀)) RingCat.{u}}
    (A : smallCrystallineSite S I γ h_compatible X x₀) :
    SheafOfModules (𝒪.over A) = A.obj.1.thickening.Modules := sorry

/-- Objectwise restriction of a sheaf of modules on `Cris(X/S)` to the thickening of a
small crystalline object. -/
noncomputable def CrisModuleSheaf.restrictObj
    {𝒪 : Sheaf (smallCrystallineZariskiTopology (S := S) (I := I) (γ := γ)
      (h_compatible := h_compatible) (X := X) (x₀ := x₀)) RingCat.{u}}
    (F : SheafOfModules 𝒪) (A : smallCrystallineSite S I γ h_compatible X x₀) :
    A.obj.1.thickening.Modules :=
  Eq.mp (crisSliceModules_eq (𝒪 := 𝒪) A) (F.over A)

/-- The thickening morphism induced by a morphism of small crystalline objects. -/
def crisThickeningMap {A B : smallCrystallineSite S I γ h_compatible X x₀}
    (f : A ⟶ B) : A.obj.1.thickening ⟶ B.obj.1.thickening :=
  f.hom.thickening

/-- Pullback of the restricted small-site module sheaf along a thickening morphism
recovers the restricted module sheaf of the source. -/
theorem crisRestrictObj_pullback
    {𝒪 : Sheaf (smallCrystallineZariskiTopology (S := S) (I := I) (γ := γ)
      (h_compatible := h_compatible) (X := X) (x₀ := x₀)) RingCat.{u}}
    (F : SheafOfModules 𝒪) {A B : smallCrystallineSite S I γ h_compatible X x₀}
    (f : A ⟶ B) :
    (Scheme.Modules.pullback (crisThickeningMap f)).obj
      (CrisModuleSheaf.restrictObj F B) =
      CrisModuleSheaf.restrictObj F A := sorry

/-- Comparison of restricted module sheaves along a morphism of small crystalline objects. -/
noncomputable def CrisModuleSheaf.restrictComparison
    {𝒪 : Sheaf (smallCrystallineZariskiTopology (S := S) (I := I) (γ := γ)
      (h_compatible := h_compatible) (X := X) (x₀ := x₀)) RingCat.{u}}
    (F : SheafOfModules 𝒪) {A B : smallCrystallineSite S I γ h_compatible X x₀}
    (f : A ⟶ B) :
    (Scheme.Modules.pullback (crisThickeningMap f)).obj
      (CrisModuleSheaf.restrictObj F B) ⟶
      CrisModuleSheaf.restrictObj F A :=
  eqToHom (crisRestrictObj_pullback (𝒪 := 𝒪) F f)

/-- Canonical restriction of a site-level module sheaf on `Cris(X/S)` to small
crystalline module-sheaf data on thickenings. -/
noncomputable def CrisModuleSheaf.restrict
    {𝒪 : Sheaf (smallCrystallineZariskiTopology (S := S) (I := I) (γ := γ)
      (h_compatible := h_compatible) (X := X) (x₀ := x₀)) RingCat.{u}}
    (F : SheafOfModules 𝒪) :
    CrisModuleSheaf S I γ h_compatible X x₀ :=
  { obj := fun A ↦ CrisModuleSheaf.restrictObj F A
    comparison := fun f ↦ CrisModuleSheaf.restrictComparison F f }

/-- Objectwise, `CrisModuleSheaf.restrict F` is the thickening restriction of `F`. -/
theorem CrisModuleSheaf.restrict_obj
    {𝒪 : Sheaf (smallCrystallineZariskiTopology (S := S) (I := I) (γ := γ)
      (h_compatible := h_compatible) (X := X) (x₀ := x₀)) RingCat.{u}}
    (F : SheafOfModules 𝒪) (A : smallCrystallineSite S I γ h_compatible X x₀) :
    (CrisModuleSheaf.restrict F).obj A = CrisModuleSheaf.restrictObj F A := sorry

/-- The comparison map of `CrisModuleSheaf.restrict F` is the thickening-pullback
comparison of `F`. -/
theorem CrisModuleSheaf.restrict_comparison
    {𝒪 : Sheaf (smallCrystallineZariskiTopology (S := S) (I := I) (γ := γ)
      (h_compatible := h_compatible) (X := X) (x₀ := x₀)) RingCat.{u}}
    (F : SheafOfModules 𝒪) {A B : smallCrystallineSite S I γ h_compatible X x₀}
    (f : A ⟶ B) :
    (CrisModuleSheaf.restrict F).comparison f =
      CrisModuleSheaf.restrictComparison F f := sorry

end
