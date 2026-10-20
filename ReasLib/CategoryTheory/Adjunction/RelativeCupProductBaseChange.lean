/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.CommSq
public import ReasLib.CategoryTheory.Adjunction.BaseChange
public import ReasLib.CategoryTheory.Adjunction.RelativeCupProduct
import Mathlib.Tactic.CrossRefAttribute

/-!
# Base change for relative cup products

This file records the compatibility between the relative cup product induced by an adjunction and
the right mate of a square of left adjoints.  The statement is categorical: derived categories and
geometric functors enter only through later specializations.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe uX uX' uY uY' vX vX' vY vY'

namespace CategoryTheory

section

variable {DX : Type uX} {DX' : Type uX'} {DY : Type uY} {DY' : Type uY'}
variable [Category.{vX} DX] [Category.{vX'} DX']
variable [Category.{vY} DY] [Category.{vY'} DY']

/-- Lemma 21.33.5: the relative cup product is compatible with canonical derived base-change maps
when the square isomorphism is compatible with the four pullback-tensor comparisons. -/
@[stacks 0H9A]
theorem relativeDerivedCupProduct_baseChange_commSq
    {Lf : DY ⥤ DX} {Lf' : DY' ⥤ DX'} {Lg : DY ⥤ DY'} {Lg' : DX ⥤ DX'}
    {Rf : DX ⥤ DY} {Rf' : DX' ⥤ DY'}
    (tensorX : DX ⥤ DX ⥤ DX) (tensorX' : DX' ⥤ DX' ⥤ DX')
    (tensorY : DY ⥤ DY ⥤ DY) (tensorY' : DY' ⥤ DY' ⥤ DY')
    (adj_f : Lf ⊣ Rf) (adj_f' : Lf' ⊣ Rf')
    (squareIso : Lg ⋙ Lf' ≅ Lf ⋙ Lg')
    (pullbackTensorIso_f :
      ∀ A B : DY,
        Lf.obj ((tensorY.obj B).obj A) ≅
          ((tensorX.obj (Lf.obj B)).obj (Lf.obj A)))
    (pullbackTensorIso_f' :
      ∀ A B : DY',
        Lf'.obj ((tensorY'.obj B).obj A) ≅
          ((tensorX'.obj (Lf'.obj B)).obj (Lf'.obj A)))
    (pullbackTensorIso_g :
      ∀ A B : DY,
        Lg.obj ((tensorY.obj B).obj A) ≅
          ((tensorY'.obj (Lg.obj B)).obj (Lg.obj A)))
    (pullbackTensorIso_g' :
      ∀ A B : DX,
        Lg'.obj ((tensorX.obj B).obj A) ≅
          ((tensorX'.obj (Lg'.obj B)).obj (Lg'.obj A)))
    (squareIsoTensorCommSq :
      ∀ A B : DY,
        CommSq
          (Lf'.map (pullbackTensorIso_g A B).hom)
          (squareIso.hom.app ((tensorY.obj B).obj A))
          (pullbackTensorIso_f' (Lg.obj A) (Lg.obj B)).hom
          (Lg'.map (pullbackTensorIso_f A B).hom ≫
            (pullbackTensorIso_g' (Lf.obj A) (Lf.obj B)).hom ≫
            (tensorX'.map (squareIso.inv.app B)).app (Lg'.obj (Lf.obj A)) ≫
            (tensorX'.obj (Lf'.obj (Lg.obj B))).map (squareIso.inv.app A)))
    (K L : DX) :
    let ηK := DerivedBaseChange.app adj_f adj_f' squareIso K
    let ηL := DerivedBaseChange.app adj_f adj_f' squareIso L
    let ηKL := DerivedBaseChange.app adj_f adj_f' squareIso ((tensorX.obj L).obj K)
    CommSq
      (Lg.map
        (adj_f.relativeDerivedCupProduct tensorY tensorX
          (fun A B ↦ (pullbackTensorIso_f B A).hom) L K))
      ((pullbackTensorIso_g (Rf.obj K) (Rf.obj L)).hom ≫
        (tensorY'.map ηL).app (Lg.obj (Rf.obj K)) ≫
        (tensorY'.obj (Rf'.obj (Lg'.obj L))).map ηK)
      (ηKL ≫ Rf'.map (pullbackTensorIso_g' K L).hom)
      (adj_f'.relativeDerivedCupProduct tensorY' tensorX'
        (fun A B ↦ (pullbackTensorIso_f' B A).hom) (Lg'.obj L) (Lg'.obj K)) := sorry

end

end CategoryTheory
