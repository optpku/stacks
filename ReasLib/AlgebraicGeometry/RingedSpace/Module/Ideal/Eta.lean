/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal.Torsion
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Ideal.Action.HomologicalComplex
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.InvertiblePower.Comparison
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TensorUnit
import Mathlib.Tactic.CrossRefAttribute

/-!
# The Berthelot-Ogus eta complex of an ideal sheaf

For an ideal sheaf whose underlying module is tensor-invertible and a cochain complex `K` on which
the ideal acts monomorphically in every degree, this file constructs the complex `η[I] K`.  The
construction is owned here, independently of any local chart, derived-category presentation, or
chapter file.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory ComplexShape
open SheafOfModules.RingedSite.IdealSheaf

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.IdealSheaf.Eta

variable {X : RingedSpace.{u}}

/-- The canonical domain of the ideal-sheaf eta construction. -/
abbrev Domain
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules)) :=
  IsActionMono.Complexes I (up ℤ)

/-- The tensor term `I^⊗ i ⊗ K^j` used in the Berthelot-Ogus construction. -/
noncomputable abbrev tensorTerm
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    [isInvertibleObject (I : X.Modules)]
    (K : CochainComplex X.Modules ℤ) (i j : ℤ) : X.Modules :=
  (I : X.Modules) ^⊗ i ⊗ K.X j

/-- The degree-`i` ambient term `I^⊗ i ⊗ K^i`. -/
noncomputable abbrev ambient
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    [isInvertibleObject (I : X.Modules)]
    (K : CochainComplex X.Modules ℤ) (i : ℤ) : X.Modules :=
  tensorTerm I K i i

/-- The off-diagonal term `I^⊗ i ⊗ K^(i + 1)` receiving the ambient differential. -/
noncomputable abbrev differentialTarget
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    [isInvertibleObject (I : X.Modules)]
    (K : CochainComplex X.Modules ℤ) (i : ℤ) : X.Modules :=
  tensorTerm I K i (i + 1)

/-- The differential of `K`, tensored on the left by `I^⊗ i`. -/
noncomputable def ambientDifferential
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    [isInvertibleObject (I : X.Modules)]
    (K : CochainComplex X.Modules ℤ) (i : ℤ) :
    ambient I K i ⟶ differentialTarget I K i :=
  tensorHom (𝟙 ((I : X.Modules) ^⊗ i)) (K.d i (i + 1))

/-- The canonical map `I^⊗ (i + 1) ⊗ K^(i + 1) ⟶ I^⊗ i ⊗ K^(i + 1)`. -/
noncomputable def succInclusion
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    [isInvertibleObject (I : X.Modules)]
    (K : CochainComplex X.Modules ℤ) (i : ℤ) :
    ambient I K (i + 1) ⟶ differentialTarget I K i :=
  (tensorHom (RingedSpace.InvertiblePower.oneAddIso (I : X.Modules) i).symm.hom
      (𝟙 (K.X (i + 1))) ≫
    (α_ (I : X.Modules) ((I : X.Modules) ^⊗ i) (K.X (i + 1))).hom) ≫
    action I (differentialTarget I K i)

/-- The quotient of the off-diagonal term by the next tensor-power term. -/
noncomputable abbrev quotient
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    [isInvertibleObject (I : X.Modules)]
    (K : CochainComplex X.Modules ℤ) (i : ℤ) : X.Modules :=
  cokernel (succInclusion I K i)

/-- The ambient differential followed by the canonical quotient projection. -/
noncomputable def toQuotient
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    [isInvertibleObject (I : X.Modules)]
    (K : CochainComplex X.Modules ℤ) (i : ℤ) :
    ambient I K i ⟶ quotient I K i :=
  ambientDifferential I K i ≫ cokernel.π (succInclusion I K i)

/-- The degree-`i` object of the Berthelot-Ogus eta complex. -/
noncomputable def obj
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    [isInvertibleObject (I : X.Modules)]
    (K : CochainComplex X.Modules ℤ) (i : ℤ) : X.Modules :=
  kernel (toQuotient I K i)

/-- For a termwise action-monic complex, the next-power inclusion is monomorphic. -/
instance succInclusion_mono
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    [isInvertibleObject (I : X.Modules)] (K : CochainComplex X.Modules ℤ)
    [IsActionMono.Complex I K] (i : ℤ) : Mono (succInclusion I K i) := sorry

/-- The ambient differential from an eta term vanishes after quotienting by the next power. -/
theorem next_w
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    [isInvertibleObject (I : X.Modules)]
    (K : CochainComplex X.Modules ℤ) (i : ℤ) :
    (kernel.ι (toQuotient I K i) ≫ ambientDifferential I K i) ≫
      cokernel.π (succInclusion I K i) = 0 := sorry

/-- The divided ambient differential from the degree-`i` eta term to the next ambient term. -/
noncomputable def next
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    [isInvertibleObject (I : X.Modules)] (K : CochainComplex X.Modules ℤ)
    [IsActionMono.Complex I K] (i : ℤ) : obj I K i ⟶ ambient I K (i + 1) :=
  CategoryTheory.Abelian.monoLift (succInclusion I K i)
    (kernel.ι (toQuotient I K i) ≫ ambientDifferential I K i) (next_w I K i)

/-- The divided ambient differential lands in the next eta term. -/
theorem next_comp_toQuotient
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    [isInvertibleObject (I : X.Modules)] (K : CochainComplex X.Modules ℤ)
    [IsActionMono.Complex I K] (i : ℤ) :
    next I K i ≫ toQuotient I K (i + 1) = 0 := sorry

/-- The differential of the Berthelot-Ogus eta complex. -/
noncomputable def d
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    [isInvertibleObject (I : X.Modules)] (K : CochainComplex X.Modules ℤ)
    [IsActionMono.Complex I K] (i : ℤ) : obj I K i ⟶ obj I K (i + 1) :=
  kernel.lift (toQuotient I K (i + 1)) (next I K i) (next_comp_toQuotient I K i)

/-- Successive Berthelot-Ogus differentials compose to zero. -/
theorem d_sq
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    [isInvertibleObject (I : X.Modules)] (K : CochainComplex X.Modules ℤ)
    [IsActionMono.Complex I K] (i : ℤ) : d I K i ≫ d I K (i + 1) = 0 := sorry

/-- The sheaf-level Berthelot-Ogus eta complex `η[I] K`. -/
@[stacks 0F8N "Berthelot-Ogus eta complex"]
noncomputable def complex
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    [isInvertibleObject (I : X.Modules)] (K : CochainComplex X.Modules ℤ)
    [IsActionMono.Complex I K] : CochainComplex X.Modules ℤ :=
  CochainComplex.of (obj I K) (d I K) (d_sq I K)

/-- Lemma 20.55.5 (0F8N): the `i`th homology of `η[I] K` is isomorphic to
`I^⊗ i ⊗ (H^i(K) / H^i(K)[I])`. -/
@[stacks 0F8N]
theorem tensorPower_torsionQuotient_isomorphic_homology
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    [isInvertibleObject (I : X.Modules)] (K : CochainComplex X.Modules ℤ)
    [IsActionMono.Complex I K] [CategoryWithHomology X.Modules] (i : ℤ) :
    IsIsomorphic
      (((I : X.Modules) ^⊗ i) ⊗
        torsionQuotient (O := X.sheaf) I (K.homology i))
      ((complex I K).homology i) := sorry

end AlgebraicGeometry.RingedSpace.IdealSheaf.Eta

namespace IdealEta

/-- Scoped notation for the Berthelot-Ogus eta complex of an ideal sheaf. -/
scoped notation "η[" I "]" =>
  AlgebraicGeometry.RingedSpace.IdealSheaf.Eta.complex I

end IdealEta
