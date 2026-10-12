/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Cech.Underlying
public import ReasLib.Algebra.Homology.CochainComplex.Nat.Derived.Exact
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cech.Derived
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cech.Sections
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Sections.Forget
public import ReasLib.CategoryTheory.Sites.Cech.Precomp
public import ReasLib.Topology.Opens.Cover
import Mathlib.Tactic.CrossRefAttribute

/-!
# Underlying additive Cech complexes of module sheaves

For an indexed open cover, the module-valued Cech complex formed on the slice over the covered
open becomes, after forgetting the section-ring action, the established additive Cech complex of
the indexed family.  This file exposes the comparison at the complex, derived, and cohomology
levels, with no per-degree choice data.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleCech.Underlying

variable {X : RingedSpace.{u}}
variable (U : Opens X.carrier) {ι : Type u}
variable (𝒰 : ι → Opens X.carrier) (h𝒰 : iSup 𝒰 = U)

/-- The slice-site module Cech complex after forgetting its `Γ(U, 𝒪_X)`-module structure. -/
@[stacks 01EQ "forgotten slice-site module Cech source"]
abbrev complexSource : X.Modules ⥤ CochainComplex AddCommGrpCat.{u} ℕ :=
  SheafOfModules.forget X.ringCatSheaf ⋙
    SheafOfModules.RingedSite.Cech.Underlying.complexSource
      X.ringCatSheaf U (Opens.Cover.overFamily U 𝒰 h𝒰)

/-- Forgetting the section-module structure identifies the slice-site module Cech complex with
the ordinary additive Cech complex of the indexed open family. -/
@[stacks 01EQ "underlying additive module Cech complex"]
noncomputable def complexIso :
    complexSource U 𝒰 h𝒰 ≅ moduleCechComplexFunctor 𝒰 :=
  Functor.isoWhiskerLeft (SheafOfModules.forget X.ringCatSheaf)
      (SheafOfModules.RingedSite.Cech.Underlying.complexIso
        X.ringCatSheaf U (Opens.Cover.overFamily U 𝒰 h𝒰)) ≪≫
    (Functor.associator
      (SheafOfModules.forget X.ringCatSheaf)
      (PresheafOfModules.toPresheaf X.ringCatSheaf.obj)
      (cechComplexOnPresheaves U (Opens.Cover.overFamily U 𝒰 h𝒰))).symm ≪≫
    Functor.isoWhiskerRight (moduleUnderlyingPresheafIso X).symm
      (cechComplexOnPresheaves U (Opens.Cover.overFamily U 𝒰 h𝒰)) ≪≫
    Functor.isoWhiskerLeft (moduleUnderlyingPresheaf X)
      (CategoryTheory.Cech.Precomp.complexIso (A := AddCommGrpCat.{u})
        (Over.forget U) (Opens.Cover.overFamily U 𝒰 h𝒰))

/-- The forgotten slice Cech complex, extended by zero and localized in the unbounded additive
derived category. -/
@[stacks 01EQ "forgotten derived slice-site module Cech source"]
abbrev derivedSource : X.Modules ⥤ DerivedCategory AddCommGrpCat.{u} :=
  complexSource U 𝒰 h𝒰 ⋙
    CochainComplex.Plus.extendNat AddCommGrpCat.{u} ⋙
    DerivedCategory.Plus.Q ⋙ DerivedCategory.Plus.ι

/-- The derived object of the forgotten slice-site module Cech complex is canonically the
established derived additive Cech object of the indexed open family. -/
@[stacks 01EQ "underlying additive derived module Cech complex"]
noncomputable def derivedIso :
    derivedSource U 𝒰 h𝒰 ≅
      AlgebraicGeometry.RingedSpace.ModuleCech.derivedFunctor 𝒰 :=
  Functor.isoWhiskerRight (complexIso U 𝒰 h𝒰)
    (CochainComplex.Plus.extendNat AddCommGrpCat.{u} ⋙
      DerivedCategory.Plus.Q ⋙ DerivedCategory.Plus.ι)

/-- The comparison between the two derived Cech sources at one module sheaf: first localizing
the module-valued Cech complex and then deriving the section-module forgetful functor agrees
canonically with the established additive derived Cech object. -/
@[stacks 01EQ "underlying additive derived module Cech comparison object"]
noncomputable def sourceForgetAppIso (F : X.Modules) :
    ((AlgebraicGeometry.RingedSpace.ModuleCech.derivedSource U
        (Opens.Cover.overFamily U 𝒰 h𝒰) ⋙
      AlgebraicGeometry.RingedSpace.Module.Derived.Sections.underlyingDerivedFunctor X U).obj F) ≅
      (AlgebraicGeometry.RingedSpace.ModuleCech.derivedFunctor 𝒰).obj F :=
  (CategoryTheory.ExactFunctor.Derived.Nat.iso
      (AlgebraicGeometry.RingedSpace.Module.Derived.Sections.exactForget X U)).app
        ((AlgebraicGeometry.RingedSpace.ModuleCech.complex U
          (Opens.Cover.overFamily U 𝒰 h𝒰)).obj F) ≪≫
    (derivedIso U 𝒰 h𝒰).app F

/-- The objectwise comparisons from module-valued to additive derived Cech sources are natural
in the module sheaf. -/
@[stacks 01EQ "naturality of the underlying additive derived module Cech comparison"]
theorem sourceForgetAppIso_hom_naturality {F G : X.Modules} (f : F ⟶ G) :
    (AlgebraicGeometry.RingedSpace.ModuleCech.derivedSource U
        (Opens.Cover.overFamily U 𝒰 h𝒰) ⋙
      AlgebraicGeometry.RingedSpace.Module.Derived.Sections.underlyingDerivedFunctor X U).map f ≫
        (sourceForgetAppIso U 𝒰 h𝒰 G).hom =
      (sourceForgetAppIso U 𝒰 h𝒰 F).hom ≫
        (AlgebraicGeometry.RingedSpace.ModuleCech.derivedFunctor 𝒰).map f := sorry

/-- Forgetting the section-module structure after forming the module-valued derived Cech source
canonically recovers the additive derived Cech functor of the indexed open family. -/
@[stacks 01EQ "underlying additive derived module Cech source"]
noncomputable def sourceForgetIso :
    AlgebraicGeometry.RingedSpace.ModuleCech.derivedSource U
        (Opens.Cover.overFamily U 𝒰 h𝒰) ⋙
      AlgebraicGeometry.RingedSpace.Module.Derived.Sections.underlyingDerivedFunctor X U ≅
    AlgebraicGeometry.RingedSpace.ModuleCech.derivedFunctor 𝒰 :=
  NatIso.ofComponents (sourceForgetAppIso U 𝒰 h𝒰)
    (fun f ↦ sourceForgetAppIso_hom_naturality U 𝒰 h𝒰 f)

/-- Degree-`p` slice-site module Cech cohomology after forgetting the section-ring action. -/
@[stacks 01EQ "forgotten slice-site module Cech cohomology source"]
abbrev homologySource (p : ℕ) : X.Modules ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.forget X.ringCatSheaf ⋙
    SheafOfModules.RingedSite.cechComplex
      X.ringCatSheaf U (Opens.Cover.overFamily U 𝒰 h𝒰) ⋙
    HomologicalComplex.homologyFunctor
      (ModuleCat (sectionsRingOnOpen X U)) (ComplexShape.up ℕ) p ⋙
    forget₂ (ModuleCat (sectionsRingOnOpen X U)) AddCommGrpCat.{u}

/-- The underlying comparison on degree-`p` Cech cohomology of one module sheaf. -/
@[stacks 01EQ "underlying additive module Cech cohomology object"]
noncomputable def homologyAppIso (F : X.Modules) (p : ℕ) :
    (homologySource U 𝒰 h𝒰 p).obj F ≅
      (moduleCechCohomologyFunctor 𝒰 p).obj F :=
  (HomologicalComplex.mapHomologyFunctorIso
      (forget₂ (ModuleCat (sectionsRingOnOpen X U)) AddCommGrpCat.{u}) p).symm.app
        ((SheafOfModules.RingedSite.cechComplex
          X.ringCatSheaf U (Opens.Cover.overFamily U 𝒰 h𝒰)).obj
          ((SheafOfModules.forget X.ringCatSheaf).obj F)) ≪≫
    (HomologicalComplex.homologyFunctor
      AddCommGrpCat.{u} (ComplexShape.up ℕ) p).mapIso
        ((complexIso U 𝒰 h𝒰).app F)

/-- The objectwise underlying Cech-cohomology comparisons are natural in the module sheaf. -/
@[stacks 01EQ "naturality of underlying additive module Cech cohomology"]
theorem homologyAppIso_hom_naturality
    {F G : X.Modules} (f : F ⟶ G) (p : ℕ) :
    (homologySource U 𝒰 h𝒰 p).map f ≫ (homologyAppIso U 𝒰 h𝒰 G p).hom =
      (homologyAppIso U 𝒰 h𝒰 F p).hom ≫
        (moduleCechCohomologyFunctor 𝒰 p).map f := sorry

/-- Forgetting the section-module structure on slice-site module Cech cohomology canonically
recovers additive Cech cohomology of the indexed open family. -/
@[stacks 01EQ "underlying additive module Cech cohomology"]
noncomputable def homologyIso (p : ℕ) :
    homologySource U 𝒰 h𝒰 p ≅ moduleCechCohomologyFunctor 𝒰 p :=
  NatIso.ofComponents (fun F ↦ homologyAppIso U 𝒰 h𝒰 F p)
    (fun f ↦ homologyAppIso_hom_naturality U 𝒰 h𝒰 f p)

end AlgebraicGeometry.RingedSpace.ModuleCech.Underlying
