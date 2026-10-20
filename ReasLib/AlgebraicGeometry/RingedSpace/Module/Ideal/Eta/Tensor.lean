/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal.Action.Tensor
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Ideal.Eta.Functoriality
import Mathlib.Tactic.CrossRefAttribute

/-!
# Tensor compatibility of the ideal-sheaf eta complex

The eta construction commutes with termwise right tensoring by a flat module.  The comparison
is assembled from the canonical associator together with preservation of the cokernel and kernel
defining each eta term.  It is exposed as a natural isomorphism on the canonical action-monic
domain; the invertible specialization is the source-facing form of Lemma 20.55.9.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory ComplexShape
open SheafOfModules.RingedSite.IdealSheaf

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.IdealSheaf.Eta.Tensor

variable {X : RingedSpace.{u}}
variable (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
variable [isInvertibleObject (I : X.Modules)]

/-- Termwise right tensoring of cochain complexes by a fixed module. -/
abbrev complexFunctor (L : X.Modules) :
    CochainComplex X.Modules ℤ ⥤ CochainComplex X.Modules ℤ :=
  (tensorRight L).mapHomologicalComplex (up ℤ)

/-- A flat right tensor factor preserves membership in the canonical eta domain. -/
theorem domainFunctor_mem (L : X.Modules) [IsFlat L] (K : Domain I) :
    IsActionMono.complex I (up ℤ) ((complexFunctor L).obj K.obj) := sorry

/-- Termwise right tensoring by a flat module, restricted to the canonical eta domain. -/
noncomputable def domainFunctor (L : X.Modules) [IsFlat L] : Domain I ⥤ Domain I :=
  ObjectProperty.lift _
    ((IsActionMono.complex I (up ℤ)).ι ⋙ complexFunctor L)
    (domainFunctor_mem I L)

/-- Reassociation identifies a right tensor of an eta ambient term with the corresponding
ambient term after tensoring the input complex. -/
noncomputable def ambientIso
    (K : CochainComplex X.Modules ℤ) (L : X.Modules) (i : ℤ) :
    (tensorRight L).obj (Eta.ambient I K i) ≅
      Eta.ambient I ((complexFunctor L).obj K) i :=
  α_ ((I : X.Modules) ^⊗ i) (K.X i) L

/-- Reassociation identifies the right tensor of an eta differential target with the target
formed after tensoring the input complex. -/
noncomputable def differentialTargetIso
    (K : CochainComplex X.Modules ℤ) (L : X.Modules) (i : ℤ) :
    (tensorRight L).obj (Eta.differentialTarget I K i) ≅
      Eta.differentialTarget I ((complexFunctor L).obj K) i :=
  α_ ((I : X.Modules) ^⊗ i) (K.X (i + 1)) L

/-- The ambient eta differential commutes with right tensoring after canonical reassociation. -/
theorem ambientDifferential_commSq
    (K : CochainComplex X.Modules ℤ) (L : X.Modules) (i : ℤ) :
    CommSq
      (ambientIso I K L i).hom
      ((tensorRight L).map (Eta.ambientDifferential I K i))
      (Eta.ambientDifferential I ((complexFunctor L).obj K) i)
      (differentialTargetIso I K L i).hom := sorry

/-- The inclusion of the next ideal power commutes with right tensoring after reassociation. -/
theorem succInclusion_commSq
    (K : CochainComplex X.Modules ℤ) (L : X.Modules) (i : ℤ) :
    CommSq
      (ambientIso I K L (i + 1)).hom
      ((tensorRight L).map (Eta.succInclusion I K i))
      (Eta.succInclusion I ((complexFunctor L).obj K) i)
      (differentialTargetIso I K L i).hom := sorry

/-- A flat right tensor factor carries the cokernel in the eta construction to the cokernel
formed after tensoring the input complex. -/
noncomputable def quotientIso
    (K : CochainComplex X.Modules ℤ) (L : X.Modules) [IsFlat L] (i : ℤ) :
    (tensorRight L).obj (Eta.quotient I K i) ≅
      Eta.quotient I ((complexFunctor L).obj K) i :=
  (PreservesCokernel.iso (tensorRight L) (Eta.succInclusion I K i)) ≪≫
    cokernel.mapIso
      ((tensorRight L).map (Eta.succInclusion I K i))
      (Eta.succInclusion I ((complexFunctor L).obj K) i)
      (ambientIso I K L (i + 1))
      (differentialTargetIso I K L i)
      (succInclusion_commSq I K L i).w.symm

/-- The defining map to the eta quotient commutes with flat right tensoring. -/
theorem toQuotient_commSq
    (K : CochainComplex X.Modules ℤ) (L : X.Modules) [IsFlat L] (i : ℤ) :
    CommSq
      (ambientIso I K L i).hom
      ((tensorRight L).map (Eta.toQuotient I K i))
      (Eta.toQuotient I ((complexFunctor L).obj K) i)
      (quotientIso I K L i).hom := sorry

/-- A flat right tensor factor carries each eta term to the corresponding eta term of the
tensored complex. -/
noncomputable def objIso
    (K : CochainComplex X.Modules ℤ) (L : X.Modules) [IsFlat L] (i : ℤ) :
    (tensorRight L).obj (Eta.obj I K i) ≅
      Eta.obj I ((complexFunctor L).obj K) i :=
  (PreservesKernel.iso (tensorRight L) (Eta.toQuotient I K i)) ≪≫
    kernel.mapIso
      ((tensorRight L).map (Eta.toQuotient I K i))
      (Eta.toQuotient I ((complexFunctor L).obj K) i)
      (ambientIso I K L i)
      (quotientIso I K L i)
      (toQuotient_commSq I K L i).w.symm

/-- The termwise eta comparison intertwines the differentials. -/
theorem objIso_comm
    (K : CochainComplex X.Modules ℤ) [IsActionMono.Complex I K]
    (L : X.Modules) [IsFlat L] (i j : ℤ) (hij : (up ℤ).Rel i j) :
    (objIso I K L i).hom ≫
        (Eta.complex I ((complexFunctor L).obj K)).d i j =
      ((complexFunctor L).obj (Eta.complex I K)).d i j ≫
        (objIso I K L j).hom := sorry

/-- The eta complex of a termwise tensor product with a flat module is canonically isomorphic
to the termwise tensor product of the eta complex. -/
@[stacks 0F9W "flat tensor generalization"]
noncomputable def complexIso
    (K : CochainComplex X.Modules ℤ) [IsActionMono.Complex I K]
    (L : X.Modules) [IsFlat L] :
    Eta.complex I ((complexFunctor L).obj K) ≅
      (complexFunctor L).obj (Eta.complex I K) :=
  (HomologicalComplex.Hom.isoOfComponents
    (fun i ↦ objIso I K L i)
    (fun i j hij ↦ objIso_comm I K L i j hij)).symm

/-- The flat tensor comparison of eta complexes is natural in the action-monic complex. -/
theorem complexIso_naturality
    {K M : CochainComplex X.Modules ℤ}
    [IsActionMono.Complex I K] [IsActionMono.Complex I M]
    (f : K ⟶ M) (L : X.Modules) [IsFlat L] :
    Eta.map I ((complexFunctor L).map f) ≫ (complexIso I M L).hom =
      (complexIso I K L).hom ≫ (complexFunctor L).map (Eta.map I f) := sorry

/-- Flat right tensoring commutes naturally with the eta functor on its canonical domain. -/
@[stacks 0F9W "natural flat tensor comparison"]
noncomputable def comparison (L : X.Modules) [IsFlat L] :
    domainFunctor I L ⋙ Eta.functor I ≅
      Eta.functor I ⋙ complexFunctor L :=
  NatIso.ofComponents
    (fun K ↦ complexIso I K.obj L)
    (fun f ↦ complexIso_naturality I f.hom L)

/-- Lemma 20.55.9 (0F9W): for an invertible module `L`, the eta complex of `K ⊗ L`
is canonically isomorphic to `η[I] K ⊗ L`. -/
@[stacks 0F9W]
noncomputable def isoApp
    (L : X.Modules) [isInvertibleObject L] (K : Domain I) :
    (Eta.functor I).obj ((domainFunctor I L).obj K) ≅
      (complexFunctor L).obj ((Eta.functor I).obj K) :=
  (comparison I L).app K

end AlgebraicGeometry.RingedSpace.IdealSheaf.Eta.Tensor
