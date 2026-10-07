module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
public import Mathlib.AlgebraicGeometry.AffineScheme
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Subobject
public import ReasLib.AlgebraicGeometry.Scheme.Module.FittingIdeal
public import stacks_project.Chap66.Lemma_66_18_6_Site
public import stacks_project.Chap70.Lemma_70_14_4_Pullback
public import stacks_project.Chap71.Lemma_71_2_1_Pullback

/-!
# Fitting ideals of modules on algebraic spaces

The `i`th Fitting ideal of an `𝒪_X`-module on an algebraic space is the largest
ideal subobject of `𝒪_X` whose sections over affine étale charts recover the
scheme-theoretic Fitting ideals of the pulled-back module.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The `i`th Fitting ideal of `F` on an affine étale chart, computed as the
scheme Fitting ideal of the pullback of `F` to the underlying affine scheme. -/
def affineChartFittingIdeal {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) (i : ℕ) (U : affineEtaleSite X) :
    Ideal Γ(U.obj.left.left, ⊤) :=
  (Scheme.fittingIdealSheaf (Modules.pullbackToScheme U.obj.hom F) i).ideal
    ⟨⊤, isAffineOpen_top U.obj.left.left⟩

/-- Restriction from an étale object to an affine étale chart, as a ring
homomorphism into global sections of the chart. -/
def affineEtaleRestrict {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U : smallEtaleSite X} (V : affineEtaleSite X) (f : V.obj ⟶ U) :
    (structureSheaf X).obj.obj (op U) →+* Γ(V.obj.left.left, ⊤) :=
  ((structureSheaf X).obj.map f.op).hom

/-- Objectwise, the Fitting ideal of `F` is the largest ideal of `𝒪_X` that
restricts into the affine-étale scheme Fitting ideals. -/
def fittingIdealSubmodule {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) (i : ℕ) :
    (SheafOfModules.unit (structureSheaf X)).val.Submodule where
  obj U :=
    ⨅ (V : affineEtaleSite X), ⨅ (f : V.obj ⟶ U.unop),
      (affineChartFittingIdeal F i V).comap (affineEtaleRestrict V f)
  map _ := sorry

/-- The Fitting ideal of `F` as an `𝒪_X`-module sheaf. -/
def fittingIdealSheafModule {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) (i : ℕ) : X.Modules where
  val := (fittingIdealSubmodule F i).toPresheafOfModules
  isSheaf := sorry

/-- The canonical inclusion of the Fitting module of `F` into `𝒪_X`. -/
def fittingIdealSheafι {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) (i : ℕ) :
    fittingIdealSheafModule F i ⟶ SheafOfModules.unit (structureSheaf X) where
  val := (fittingIdealSubmodule F i).ι

/-- The Fitting inclusion is a monomorphism. -/
instance fittingIdealSheafι_mono {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) (i : ℕ) : Mono (fittingIdealSheafι F i) :=
  (SheafOfModules.forget (structureSheaf X)).mono_of_mono_map
    (inferInstance : Mono (fittingIdealSubmodule F i).ι)

/-- The `i`th Fitting ideal sheaf of an `𝒪_X`-module, as an ideal subobject of
`𝒪_X` on the small étale site. -/
def fittingIdealSheaf {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) (i : ℕ) : IdealSubobject X :=
  Subobject.mk (fittingIdealSheafι F i)

/-- Sections of `fittingIdealSheaf F i` over an étale object are the objectwise
Fitting submodule. -/
theorem fittingIdealSheaf_sections {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) (i : ℕ) (U : (smallEtaleSite X)ᵒᵖ) :
    SheafOfModules.Subobject.sections (fittingIdealSheaf F i) U =
      (fittingIdealSubmodule F i).obj U :=
  sorry

/-- A global section of `𝒪_X` over `U` lies in `fittingIdealSheaf F i` if and
only if it lies in the objectwise Fitting submodule. -/
theorem mem_fittingIdealSheaf_sections {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) (i : ℕ) (U : (smallEtaleSite X)ᵒᵖ)
    (s : (SheafOfModules.unit (structureSheaf X)).val.obj U) :
    s ∈ SheafOfModules.Subobject.sections (fittingIdealSheaf F i) U ↔
      s ∈ (fittingIdealSubmodule F i).obj U :=
  sorry

/-- On an affine étale chart, sections of `fittingIdealSheaf F i` recover the
scheme Fitting ideal of the pulled-back module. -/
theorem fittingIdealSheaf_affineEtale {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent] (i : ℕ)
    (U : affineEtaleSite X) :
    SheafOfModules.Subobject.sections (fittingIdealSheaf F i) (op U.obj) =
      (affineChartFittingIdeal F i U).comap (affineEtaleRestrict U (𝟙 U.obj)) :=
  sorry

namespace fittingIdealSheaf

/-- The Fitting ideal of a finite-type quasi-coherent module is quasi-coherent
as an `𝒪_X`-module. -/
instance instIsQuasicoherent {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent] (i : ℕ) :
    (fittingIdealSheaf F i : X.Modules).IsQuasicoherent :=
  sorry

end fittingIdealSheaf

end AlgebraicGeometry.AlgebraicSpace

