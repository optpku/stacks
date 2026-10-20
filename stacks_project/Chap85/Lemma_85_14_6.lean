/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap85.Lemma_85_14_2_System
public import stacks_project.Chap85.Lemma_85_11_1_Flat

/-!
# Lemma 85.14.6

In Situation 85.3.3, a morphism of associated simplicial systems of objects
`K, K'` of `D(O)` is induced by a morphism `K ⟶ K'` when every `f_φ⁻¹ O_n ⟶ O_m`
is flat, `K` is cartesian, and `Hom(K_i⟦i - 1⟧, K'_i) = 0` for `i > 1`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.SimplicialSites
open RingedSite

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [instMorphismDiagram : IsMorphismDiagram C J]
variable [instWeakSheafify : ∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [instLeftKan : ∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
include instMorphismDiagram instWeakSheafify instLeftKan
variable (O : Sheaf (topology C J) RingCat.{w})
variable [(topology C J).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget RingCat.{w})]
variable [UnivLE.{max u v, w}]
variable [∀ n, HasSheafify ((J n).toGrothendieck) (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w,
    (ofStage C n).op.HasPointwiseRightKanExtension P]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (stageMorphism C J O n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w}
      (ringedToposMap C J O φ).structureMap).IsRightAdjoint]
variable [∀ n, ToposHom.HasModulePullbackDerived (stageMorphism C J O n)]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    ToposHom.HasModulePullbackDerived (ringedToposMap C J O φ)]

/-- Lemma 85.14.6
In Situation 85.3.3, let `O` be a sheaf of rings on `C_total`. If `K, K'` are
objects of `D(O)`, assume `f_φ⁻¹ O_n ⟶ O_m` is flat for `φ : m ⟶ n`, `K` is
cartesian, and `Hom(K_i⟦i - 1⟧, K'_i) = 0` for `i > 1`. Then every morphism of
associated simplicial systems `{K_n ⟶ K'_n}` comes from a morphism `K ⟶ K'` in
`D(O)`. -/
@[stacks 0D9S]
theorem exists_hom_of_toDerivedModuleSystemHom
    (K K' : Hom.ModuleDerived.{w} (totalRingedSite C J O))
    [ModuleDerived.IsCartesian C J O K]
    (h_flat : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
      ToposHom.IsFlat (ringedToposMap C J O φ))
    (h_hom : ∀ (n : SimplexCategory), 1 < n.len →
      Subsingleton
        (((toDerivedModuleSystem C J O K).obj n)⟦(n.len : ℤ) - 1⟧ ⟶
          (toDerivedModuleSystem C J O K').obj n))
    (α : DerivedModuleSystem.Hom (toDerivedModuleSystem C J O K)
      (toDerivedModuleSystem C J O K')) :
    ∃ f : K ⟶ K', ∀ n, (toDerivedModuleSystemMap C J O f).app n = α.app n :=
  sorry

end CategoryTheory.SimplicialSites
