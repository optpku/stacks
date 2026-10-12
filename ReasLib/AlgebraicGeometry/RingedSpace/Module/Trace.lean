/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Grothendieck
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.InternalHom
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.LocallyFree.Dualizable
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Monoidal
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TensorUnit
public import ReasLib.CategoryTheory.Monoidal.Closed.Dualizable
public import ReasLib.CategoryTheory.Monoidal.Closed.Exactness

/-!
# Trace of a finite locally free module sheaf

A finite locally free module `E` on a ringed space is dualizable, so evaluation against `dual E`
contracts `Hom(E, E ⊗ F)` onto `F`. Passing to `Ext` along internal Hom, the identity section,
and this sheaf-level contraction yields the generalized trace
`Ext^i(E, E ⊗ F) →+ Ext^i(𝒪_X, F)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed CategoryTheory.Abelian
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Module.Trace

variable {X : RingedSpace.{u}}

/-- Finite local freeness makes the canonical tensor-to-endomorphism comparison invertible. -/
instance isIso_tensorIhomUnitToEnd (E : X.Modules) [E.IsFiniteLocallyFree] :
    IsIso (tensorIhomUnitToEnd E) :=
  IsRightDualizable.isIso_tensorIhomUnitToEnd
    (SheafOfModules.IsFiniteLocallyFree.isRightDualizable E)

/-- Internal Hom out of a finite locally free module preserves finite colimits. -/
instance ihom_preservesFiniteColimits (E : X.Modules) [E.IsFiniteLocallyFree] :
    PreservesFiniteColimits (ihom E) := sorry

/-- Evaluation contraction `(E ⊗ F) ⊗ dual E ⟶ F`. -/
def tensorDual (E F : X.Modules) : (E ⊗ F) ⊗ dual E ⟶ F :=
  (β_ (E ⊗ F) (dual E)).hom ≫ (α_ (dual E) E F).inv ≫
    Dual.evaluation E ▷ F ≫ (λ_ F).hom

/-- Sheaf-level generalized trace `Hom(E, E ⊗ F) ⟶ F`. -/
def sheaf (E F : X.Modules) [E.IsFiniteLocallyFree] :
    (ihom E).obj (E ⊗ F) ⟶ F :=
  inv (Dual.tensorComparison E (E ⊗ F)) ≫ tensorDual E F

/-- Sheaf-level endomorphism trace `Hom(E, E) ⟶ 𝟙_ X.Modules`. -/
def sheaf_end (E : X.Modules) [E.IsFiniteLocallyFree] :
    (ihom E).obj E ⟶ 𝟙_ X.Modules :=
  (ihom E).map (ρ_ E).inv ≫ sheaf E (𝟙_ X.Modules)

/-- The identity of `E` as a global section of `Hom(E, E)`. -/
def identitySection (E : X.Modules) : 𝟙_ X.Modules ⟶ (ihom E).obj E :=
  curry' (𝟙 E)

/-- `sheaf` is the evaluation contraction after inverting `Dual.tensorComparison`. -/
theorem sheaf_spec (E F : X.Modules) [E.IsFiniteLocallyFree] :
    Dual.tensorComparison E (E ⊗ F) ≫ sheaf E F = tensorDual E F := sorry

/-- The sheaf-level trace is natural in the second module. -/
theorem sheaf_natural (E : X.Modules) [E.IsFiniteLocallyFree]
    {F F' : X.Modules} (φ : F ⟶ F') :
    (ihom E).map (E ◁ φ) ≫ sheaf E F' = sheaf E F ≫ φ := sorry

variable [HasExt X.Modules]

/-- Ext-level generalized trace `Ext^i(E, E ⊗ F) →+ Ext^i(𝒪_X, F)`. -/
def ext (E F : X.Modules) [E.IsFiniteLocallyFree] (i : ℕ) :
    Ext E (E ⊗ F) i →+ Ext (SheafOfModules.unit X.ringCatSheaf) F i :=
  let ihomExt := (ihom E).mapExtAddHom E (E ⊗ F) i
  let preId := (Ext.mk₀ (identitySection E)).precomp ((ihom E).obj (E ⊗ F)) (zero_add i)
  let postTr := (Ext.mk₀ (sheaf E F)).postcomp (𝟙_ X.Modules) (add_zero i)
  let toUnit := (Ext.mk₀ (unitIsoTensorUnit X).hom).precomp F (zero_add i)
  toUnit.comp (postTr.comp (preId.comp ihomExt))

/-- Ext-level endomorphism trace `Ext^i(E, E) →+ Ext^i(𝒪_X, 𝒪_X)`. -/
def ext_end (E : X.Modules) [E.IsFiniteLocallyFree] (i : ℕ) :
    Ext E E i →+ Ext (SheafOfModules.unit X.ringCatSheaf)
      (SheafOfModules.unit X.ringCatSheaf) i :=
  let unitor := (Ext.mk₀ (ρ_ E).inv).postcomp E (add_zero i)
  let tr := ext E (𝟙_ X.Modules) i
  let toUnit :=
    (Ext.mk₀ (unitIsoTensorUnit X).inv).postcomp
      (SheafOfModules.unit X.ringCatSheaf) (add_zero i)
  toUnit.comp (tr.comp unitor)

/-- On morphisms, `ext` is induced by the sheaf-level trace. -/
theorem ext_mk₀ (E F : X.Modules) [E.IsFiniteLocallyFree] (f : E ⟶ E ⊗ F) :
    ext E F 0 (Ext.mk₀ f) =
      Ext.mk₀
        ((unitIsoTensorUnit X).hom ≫ identitySection E ≫ (ihom E).map f ≫ sheaf E F) := sorry

/-- On endomorphisms, `ext_end` is induced by the sheaf-level endomorphism trace. -/
theorem ext_end_mk₀ {X : RingedSpace.{u}} [HasExt X.Modules]
    (E : X.Modules) [E.IsFiniteLocallyFree] (f : E ⟶ E) :
    ext_end E 0 (Ext.mk₀ f) =
      Ext.mk₀
        ((unitIsoTensorUnit X).hom ≫ identitySection E ≫
          (ihom E).map f ≫ sheaf_end E ≫ (unitIsoTensorUnit X).inv) := sorry

end AlgebraicGeometry.RingedSpace.Module.Trace
