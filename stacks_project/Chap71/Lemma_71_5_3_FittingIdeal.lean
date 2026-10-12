/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
public import Mathlib.AlgebraicGeometry.AffineScheme
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Subobject
public import ReasLib.AlgebraicGeometry.Scheme.Module.FittingIdeal
public import stacks_project.Chap66.Lemma_66_12_3
public import stacks_project.Chap66.Lemma_66_18_6_Site
public import stacks_project.Chap67.Definition_67_15_4_SchemeTheoreticSupport
public import stacks_project.Chap67.Lemma_67_13_1
public import stacks_project.Chap67.Lemma_67_15_1_ModuleSupport
public import stacks_project.Chap67.Lemma_67_15_3_SchemeTheoreticSupport
public import stacks_project.Chap71.Lemma_71_2_1_Pullback

/-!
# Closed subspace cut out by the zeroth Fitting ideal

`Fit_i(F)` is recorded as a Chap67 `IdealSubobject` whose sections over étale
objects are the largest ideals restricting into the affine-étale scheme Fitting
ideals. The closed subspace cut out by `Fit_0(F)` is
`ClosedSubspace.ofQuasiCoherentIdeal`. This owner is independent of the
Lemma 71.5.1 Fitting sheaf, which cannot be imported beside Chap67
`IdealSubobject`.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- The section ideal of `Fit_i(F)` over an étale object, as the largest ideal of
`𝒪_X(U)` that restricts into the scheme Fitting ideals on affine étale charts. -/
def fittingSectionIdeal {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) (i : ℕ) (U : (smallEtaleSite X)ᵒᵖ) :
    Ideal ((structureSheaf X).obj.obj U) :=
  ⨅ (V : affineEtaleSite X), ⨅ (f : V.obj ⟶ U.unop),
    ((Scheme.fittingIdealSheaf (pullbackToScheme V.obj.hom F) i).ideal
        ⟨⊤, isAffineOpen_top V.obj.left.left⟩).comap
      (((structureSheaf X).obj.map f.op).hom)

/-- A global section of `𝒪_X` over `U` lies in `fittingSectionIdeal F i U` if and
only if it restricts into every affine-étale scheme Fitting ideal. -/
theorem mem_fittingSectionIdeal {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) (i : ℕ) (U : (smallEtaleSite X)ᵒᵖ)
    (s : (structureSheaf X).obj.obj U) :
    s ∈ fittingSectionIdeal F i U ↔
      ∀ (V : affineEtaleSite X) (f : V.obj ⟶ U.unop),
        ((structureSheaf X).obj.map f.op).hom s ∈
          (Scheme.fittingIdealSheaf (pullbackToScheme V.obj.hom F) i).ideal
            ⟨⊤, isAffineOpen_top V.obj.left.left⟩ :=
  sorry

/-- Objectwise, `Fit_i(F)` is the submodule of `𝒪_X` with sections
`fittingSectionIdeal`. -/
def fittingSheafSubmodule {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) (i : ℕ) :
    (SheafOfModules.unit (structureSheaf X)).val.Submodule where
  obj U := fittingSectionIdeal F i U
  map _ := sorry

/-- The object of `fittingSheafSubmodule` over `U` is `fittingSectionIdeal`. -/
theorem fittingSheafSubmodule_obj {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) (i : ℕ) (U : (smallEtaleSite X)ᵒᵖ) :
    (fittingSheafSubmodule F i).obj U = fittingSectionIdeal F i U :=
  sorry

/-- The Fitting ideal of `F` as an `𝒪_X`-module sheaf. -/
def fittingSheaf {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) (i : ℕ) : X.Modules where
  val := (fittingSheafSubmodule F i).toPresheafOfModules
  isSheaf := sorry

/-- The underlying presheaf of `fittingSheaf` is the submodule associated to
`fittingSectionIdeal`. -/
theorem fittingSheaf_val {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) (i : ℕ) :
    (fittingSheaf F i).val = (fittingSheafSubmodule F i).toPresheafOfModules :=
  sorry

/-- The canonical inclusion of the Fitting module of `F` into `𝒪_X`. -/
def fittingι {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) (i : ℕ) :
    fittingSheaf F i ⟶ SheafOfModules.unit (structureSheaf X) where
  val := (fittingSheafSubmodule F i).ι

/-- The Fitting inclusion is the submodule inclusion of `fittingSheafSubmodule`. -/
theorem fittingι_val {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) (i : ℕ) :
    (fittingι F i).val = (fittingSheafSubmodule F i).ι :=
  sorry

/-- The Fitting inclusion is a monomorphism. -/
instance fittingι_mono {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) (i : ℕ) : Mono (fittingι F i) :=
  sorry

/-- The `i`th Fitting ideal of an `𝒪_X`-module, as a Chap67 ideal subobject of
`𝒪_X`. -/
def fittingIdealSubobject {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) (i : ℕ) : IdealSubobject X :=
  Subobject.mk (fittingι F i)

/-- The Fitting ideal subobject is represented by `fittingι`. -/
theorem fittingIdealSubobject_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) (i : ℕ) :
    fittingIdealSubobject F i = Subobject.mk (fittingι F i) :=
  sorry

/-- Sections of `fittingIdealSubobject F i` over an étale object are the
objectwise Fitting section ideals. -/
theorem fittingIdealSubobject_sections {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) (i : ℕ) (U : (smallEtaleSite X)ᵒᵖ) :
    SheafOfModules.Subobject.sections (fittingIdealSubobject F i) U =
      fittingSectionIdeal F i U :=
  sorry

/-- On an affine étale chart, sections of `fittingIdealSubobject F i` recover the
scheme Fitting ideal of the pulled-back module. -/
theorem fittingIdealSubobject_affineEtale {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (i : ℕ)
    (U : affineEtaleSite X) :
    SheafOfModules.Subobject.sections (fittingIdealSubobject F i) (op U.obj) =
      ((Scheme.fittingIdealSheaf (pullbackToScheme U.obj.hom F) i).ideal
          ⟨⊤, isAffineOpen_top U.obj.left.left⟩).comap
        (((structureSheaf X).obj.map (𝟙 U.obj).op).hom) :=
  sorry

/-- The Fitting ideal of a finite-type quasi-coherent module is a quasi-coherent
ideal subobject of `𝒪_X`. -/
instance instIdealIsQuasiCoherent {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (i : ℕ) :
    IsQuasiCoherent (fittingIdealSubobject F i) :=
  sorry

/-- The closed subspace of `X` cut out by the zeroth Fitting ideal of `F`. -/
def fittingIdealZeroSubspace {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] : ClosedSubspace X :=
  ClosedSubspace.ofQuasiCoherentIdeal (fittingIdealSubobject F 0)

/-- The inclusion of the zeroth Fitting closed subspace is the closed-subspace
inclusion cut out by `Fit_0(F)`. -/
theorem fittingIdealZeroSubspace_ι {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    (fittingIdealZeroSubspace F).ι = subschemeι (fittingIdealSubobject F 0) :=
  sorry

/-- The kernel ideal sheaf of the zeroth Fitting closed subspace is
`Fit_0(F)`. -/
theorem fittingIdealZeroSubspace_idealSheaf {S : Scheme.{u}}
    {X : AlgebraicSpace S} (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    (fittingIdealZeroSubspace F).idealSheaf = fittingIdealSubobject F 0 :=
  sorry

/-- The zeroth Fitting closed subspace is cut out by `Fit_0(F)`, and its
inclusion is a closed immersion. -/
theorem fittingIdealZeroSubspace_spec {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    (fittingIdealZeroSubspace F).idealSheaf = fittingIdealSubobject F 0 ∧
      IsClosedImmersion (fittingIdealZeroSubspace F).ι :=
  sorry

/-- The zeroth Fitting ideal is contained in the annihilator ideal sheaf of the
scheme-theoretic support. -/
theorem fittingIdealSubobject_zero_le_schemeTheoreticSupport
    {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    fittingIdealSubobject F 0 ≤ (schemeTheoreticSupport F).idealSheaf :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
