/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap85.Lemma_85_6_1
public import stacks_project.Chap85.Lemma_85_11_1_Flat

/-!
# Lemma 85.6.3

With assumptions as in Lemma 85.6.1, the functor `g_{n!} : Mod(O_n) ⥤ Mod(O)` is
exact if the structure maps `f_φ⁻¹ O_n ⟶ O_m` are flat for all `φ : n ⟶ m`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open RingedSite

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [IsMorphismDiagram C J]
variable (O : Sheaf (topology C J) RingCat.{w})
variable [(topology C J).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, HasSheafify ((J n).toGrothendieck) (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w,
    (ofStage C n).op.HasPointwiseRightKanExtension P]
variable [HasWeakSheafify (topology C J) (Type w)]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (stageMorphism C J O n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w} (ringedToposMap C J O φ).structureMap).IsRightAdjoint]

/-- Lemma 85.6.3 (1): with assumptions as in Lemma 85.6.1, in Situation 85.3.3 case A
the functor `g_{n!} : Mod(O_n) ⥤ Mod(O)` is exact if the maps
`f_φ⁻¹ O_n ⟶ O_m` are flat for all `φ : n ⟶ m`. -/
@[stacks 0D74]
theorem moduleLowerShriek_exact (n : SimplexCategory)
    (h_flat : ∀ {m : SimplexCategory} (φ : n ⟶ m),
      ToposHom.IsFlat (ringedToposMap C J O φ)) :
    exactFunctor
      (SheafOfModules.{w} (componentRingSheaf C J O n))
      (SheafOfModules.{w} O)
      (moduleLowerShriek C J O n) :=
  sorry

end CategoryTheory.SimplicialSites

namespace CategoryTheory.Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable [IsFiberwiseSite F J]
variable (O : Sheaf (topology F J) RingCat.{w})
variable [(topology F J).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [HasSheafify (topology F J) (Type w)]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
    (ι F (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (fiberStageMorphism F J O n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w}
      (fiberRingedToposMap F J O φ).structureMap).IsRightAdjoint]

/-- Lemma 85.6.3 (2): with assumptions as in Lemma 85.6.1, in Situation 85.3.3 case B
the functor `g_{n!} : Mod(O_n) ⥤ Mod(O)` is exact if the maps
`f_φ⁻¹ O_n ⟶ O_m` are flat for all `φ : n ⟶ m`. -/
@[stacks 0D74]
theorem fiberModuleLowerShriek_exact (n : SimplexCategory)
    (h_flat : ∀ {m : SimplexCategory} (φ : n ⟶ m),
      ToposHom.IsFlat (fiberRingedToposMap F J O φ)) :
    exactFunctor
      (SheafOfModules.{w} (fiberComponentRingSheaf F J O n))
      (SheafOfModules.{w} O)
      (fiberModuleLowerShriek F J O n) :=
  sorry

end CategoryTheory.Grothendieck
