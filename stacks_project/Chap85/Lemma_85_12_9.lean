/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap85.Lemma_85_12_9_Comparison

/-!
# Lemma 85.12.9

In Situation 85.3.3, an object of `D(C_total)` is cartesian if and only if the
canonical maps `g_{n!} K_n ⟶ g_{n!} ℤ ⊗ᴸ K` are isomorphisms for every `n`.
If `O` is a sheaf of rings on `C_total` such that `f_φ⁻¹ O_n ⟶ O_m` is flat
for every simplex operator `φ`, the same criterion holds in `D(O)` with
`g_{n!} O_n` in place of `g_{n!} ℤ`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open RingedSite

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [IsMorphismDiagram C J]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [HasWeakSheafify (topology C J) (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w, (ofStage C n).op.HasLeftKanExtension P]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [HasSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasWeakSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ AddCommGrpCat.{w},
    (ofStage C n).op.HasLeftKanExtension P]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ AddCommGrpCat.{w},
    (ofStage C n).op.HasPointwiseLeftKanExtension P]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ AddCommGrpCat.{w},
    (ofStage C n).op.HasPointwiseRightKanExtension P]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget AddCommGrpCat.{w})]

/-- Lemma 85.12.9 (1)
In Situation 85.3.3, an object `K` of `D(C_total)` is cartesian if and only if the
canonical map `g_{n!} K_n ⟶ g_{n!} ℤ ⊗ᴸ K` is an isomorphism for every `n`. -/
@[stacks 0D9E]
theorem derived_isCartesian_iff_shriekTensor
    (K : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w})) :
    Derived.IsCartesian C J K ↔
      ∀ n : SimplexCategory, IsIso (derivedShriekTensorComparison C J n K) :=
  sorry

section Modules

variable (O : Sheaf (topology C J) CommRingCat.{w})
variable [(topology C J).HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [(topology C J).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose
    (forget₂ CommRingCat.{w} RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget RingCat.{w})]
variable [UnivLE.{max u v, w}]
variable [∀ n, HasSheafify ((J n).toGrothendieck) (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w,
    (ofStage C n).op.HasPointwiseRightKanExtension P]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (stageMorphism C J (Sheaf.ringSheafOfComm O) n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w}
      (ringedToposMap C J (Sheaf.ringSheafOfComm O) φ).structureMap).IsRightAdjoint]
variable [∀ n, ToposHom.HasModulePullbackDerived
    (stageMorphism C J (Sheaf.ringSheafOfComm O) n)]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    ToposHom.HasModulePullbackDerived
      (ringedToposMap C J (Sheaf.ringSheafOfComm O) φ)]
variable [(topology C J).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ n, ((J n).toGrothendieck).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ n, (moduleInverseImage C J (Sheaf.ringSheafOfComm O) n).Monoidal]

/-- Lemma 85.12.9 (2)
In Situation 85.3.3, if `O` is a sheaf of rings on `C_total` such that the morphisms
`f_φ⁻¹ O_n ⟶ O_m` are flat for all `φ : n ⟶ m`, then an object `K` of `D(O)` is
cartesian if and only if the canonical map `g_{n!} K_n ⟶ g_{n!} O_n ⊗ᴸ K` is an
isomorphism for every `n`. -/
@[stacks 0D9E]
theorem moduleDerived_isCartesian_iff_shriekTensor
    (h_flat : ∀ {n m : SimplexCategory} (φ : n ⟶ m),
      ToposHom.IsFlat (ringedToposMap C J (Sheaf.ringSheafOfComm O) φ))
    (K : Hom.ModuleDerived.{w} (totalRingedSite C J (Sheaf.ringSheafOfComm O))) :
    ModuleDerived.IsCartesian C J (Sheaf.ringSheafOfComm O) K ↔
      ∀ n : SimplexCategory,
        IsIso (moduleDerivedShriekTensorComparison C J O h_flat n K) :=
  sorry

end Modules

end CategoryTheory.SimplicialSites
