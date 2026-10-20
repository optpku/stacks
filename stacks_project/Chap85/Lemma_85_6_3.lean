/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.Exactness
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

/- Lemma 85.6.3. Module lower shriek from a degree is exact when all outgoing
simplex operators induce flat morphisms of ringed topoi. -/
@[stacks 0D74] #check (CategoryTheory.SimplicialSites.moduleLowerShriek_exact :
  ∀ (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
    [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
    [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
    [IsMorphismDiagram C J]
    [UnivLE.{max u v, w}]
    (O : Sheaf (topology C J) RingCat.{w})
    [(topology C J).HasSheafCompose (forget RingCat.{w})]
    [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget RingCat.{w})]
    [∀ n, HasSheafify ((J n).toGrothendieck) (Type w)]
    [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w,
    (ofStage C n).op.HasPointwiseRightKanExtension P]
    [HasWeakSheafify (topology C J) (Type w)]
    (n : SimplexCategory)
    (h_flat : ∀ {m : SimplexCategory} (φ : n ⟶ m),
      ToposHom.IsFlat (ringedToposMap C J O φ)),
    exactFunctor
      (SheafOfModules.{w} (componentRingSheaf C J O n))
      (SheafOfModules.{w} O)
      (moduleLowerShriek C J O n))

end CategoryTheory.SimplicialSites

namespace CategoryTheory.Grothendieck

/- Lemma 85.6.3. Module lower shriek from a fiber is exact when all outgoing
simplex operators induce flat morphisms of ringed topoi. -/
@[stacks 0D74] #check (CategoryTheory.Grothendieck.fiberModuleLowerShriek_exact :
  ∀ (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
    [IsFiberwiseSite F J]
    [UnivLE.{max u v, w}]
    (O : Sheaf (topology F J) RingCat.{w})
    [(topology F J).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
    [∀ n, ((J n).toGrothendieck).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
    [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
    [HasSheafify (topology F J) (Type w)]
    [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
    (ι F (op n)).op.HasPointwiseRightKanExtension P]
    [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]
    (n : SimplexCategory)
    (h_flat : ∀ {m : SimplexCategory} (φ : n ⟶ m),
      ToposHom.IsFlat (fiberRingedToposMap F J O φ)),
    exactFunctor
      (SheafOfModules.{w} (fiberComponentRingSheaf F J O n))
      (SheafOfModules.{w} O)
      (fiberModuleLowerShriek F J O n))

end CategoryTheory.Grothendieck
