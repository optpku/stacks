/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.CosimplicialObject.Augmented.ExtraCodegeneracy
public import ReasLib.CategoryTheory.Endofunctor.MonadResolution.Evaluation
public import Mathlib.CategoryTheory.Monad.Algebra

/-!
# Extra codegeneracies on evaluated monad resolutions

A chosen retraction of the monad unit supplies the zeroth-coface extra codegeneracy on the
evaluated canonical resolution. The core API therefore takes a `SplitMono` for the unit; a monad
algebra is exposed only as a canonical source of that minimal datum.
-/

@[expose] public section

open CategoryTheory.CosimplicialObject
open scoped CategoryTheory.IteratedEndofunctor Simplicial

universe u v u' v'

namespace CategoryTheory.Monad

variable {C : Type u} [Category.{v} C] {T : Monad C}

namespace Realizes

/-- Transport an extra codegeneracy from any functorial image of the canonical augmented monad
resolution to the same image of an arbitrary realization. -/
@[stacks 0FKS "extra codegeneracy transported to a monad realization"]
noncomputable def extraCodegeneracy
    {D : Type u'} [Category.{v'} D] {U : CosimplicialObject (C ⥤ C)}
    (hU : T.Realizes U)
    (F : CosimplicialObject.Augmented (C ⥤ C) ⥤
      CosimplicialObject.Augmented D)
    (ed : CosimplicialObject.Augmented.ExtraCodegeneracy
      (F.obj (cosimplicialResolution.augmented T))) :
    CosimplicialObject.Augmented.ExtraCodegeneracy (F.obj hU.augmented) :=
  CosimplicialObject.Augmented.ExtraCodegeneracy.ofIso
    (Realizes.augmentedIso.map hU F).symm ed

/-- The degree-zero retraction of a transported extra codegeneracy is conjugated by the point
and cosimplicial components of the mapped realization isomorphism. -/
@[simp, stacks 0FKS "zero-retraction transported to a monad realization"]
theorem extraCodegeneracy.s'
    {D : Type u'} [Category.{v'} D] {U : CosimplicialObject (C ⥤ C)}
    (hU : T.Realizes U)
    (F : CosimplicialObject.Augmented (C ⥤ C) ⥤
      CosimplicialObject.Augmented D)
    (ed : CosimplicialObject.Augmented.ExtraCodegeneracy
      (F.obj (cosimplicialResolution.augmented T))) :
    (Realizes.extraCodegeneracy hU F ed).s' =
      (CosimplicialObject.Augmented.drop.mapIso
        (Realizes.augmentedIso.map hU F).symm).inv.app ⦋0⦌ ≫ ed.s' ≫
      (CosimplicialObject.Augmented.point.mapIso
        (Realizes.augmentedIso.map hU F).symm).hom := sorry

/-- Each map of a transported extra codegeneracy is conjugated by the corresponding degree
components of the mapped realization isomorphism. -/
@[simp, stacks 0FKS "extra-codegeneracy maps transported to a monad realization"]
theorem extraCodegeneracy.s
    {D : Type u'} [Category.{v'} D] {U : CosimplicialObject (C ⥤ C)}
    (hU : T.Realizes U)
    (F : CosimplicialObject.Augmented (C ⥤ C) ⥤
      CosimplicialObject.Augmented D)
    (ed : CosimplicialObject.Augmented.ExtraCodegeneracy
      (F.obj (cosimplicialResolution.augmented T))) (n : ℕ) :
    (Realizes.extraCodegeneracy hU F ed).s n =
      (CosimplicialObject.Augmented.drop.mapIso
        (Realizes.augmentedIso.map hU F).symm).inv.app ⦋n + 1⦌ ≫ ed.s n ≫
      (CosimplicialObject.Augmented.drop.mapIso
        (Realizes.augmentedIso.map hU F).symm).hom.app ⦋n⦌ := sorry

end Realizes

namespace Algebra

/-- The structure map of a monad algebra exhibits the monad unit at its underlying object as a
split monomorphism. -/
@[stacks 0FKS "algebra splitting of a monad unit"]
def unitSplitMono (A : Algebra T) : SplitMono (T.η.app A.A) where
  retraction := A.a
  id := A.unit

/-- The chosen retraction in the unit splitting of a monad algebra is its structure map. -/
@[simp, stacks 0FKS "retraction of the algebra unit splitting"]
theorem unitSplitMono.retraction (A : Algebra T) : A.unitSplitMono.retraction = A.a := sorry

end Algebra

namespace cosimplicialResolution.eval

namespace splitUnit

variable {X : C} (h : SplitMono (T.η.app X))

/-- The clean degreewise map underlying the extra codegeneracy from a split unit. It first
separates the leading monad factor and then applies the positive iterate to the chosen
retraction. -/
@[stacks 0FKS "iterated retraction from a split monad unit"]
def iteratedRetraction (n : ℕ) :
    (T.toFunctor ⁺⦋n + 1⦌).obj X ⟶ (T.toFunctor ⁺⦋n⦌).obj X :=
  (IteratedEndofunctor.prependIso T.toFunctor n).inv.app X ≫
    (T.toFunctor ⁺⦋n⦌).map h.retraction

/-- The degree-zero retraction of the evaluated monad resolution supplied by a split unit. -/
@[stacks 0FKS "split-unit retraction of a monad resolution"]
noncomputable def zeroRetraction :
    ((cosimplicialResolution.eval T).obj X).right ^⦋0⦌ ⟶
      ((cosimplicialResolution.eval T).obj X).left :=
  h.retraction

/-- In degree `n`, a split unit supplies the extra codegeneracy obtained by separating the
leading monad factor and applying the positive iterate to its chosen retraction. -/
@[stacks 0FKS "split-unit extra codegeneracy of a monad resolution"]
noncomputable def codegeneracy (n : ℕ) :
    ((cosimplicialResolution.eval T).obj X).right ^⦋n + 1⦌ ⟶
      ((cosimplicialResolution.eval T).obj X).right ^⦋n⦌ :=
  iteratedRetraction h n

/-- The evaluated extra-codegeneracy map is the clean iterated-retraction map on the underlying
positive iterates. -/
@[simp, stacks 0FKS "evaluated split-unit codegeneracy formula"]
theorem codegeneracy_eq_iteratedRetraction (n : ℕ) :
    codegeneracy h n = iteratedRetraction h n := sorry

/-- The split-unit retraction splits the resolution coaugmentation in degree zero. -/
@[stacks 0FKS "split-unit retraction and resolution coaugmentation"]
theorem η_comp_s' :
    ((cosimplicialResolution.eval T).obj X).hom.app ⦋0⦌ ≫ zeroRetraction h =
      𝟙 _ := sorry

/-- The first coface followed by the first split-unit extra codegeneracy factors through the
coaugmentation and its retraction. -/
@[stacks 0FKS "initial split-unit extra-codegeneracy relation"]
theorem δ₁_comp_s₀ :
    ((cosimplicialResolution.eval T).obj X).right.δ 1 ≫ codegeneracy h 0 =
      zeroRetraction h ≫
        ((cosimplicialResolution.eval T).obj X).hom.app ⦋0⦌ := sorry

/-- Every split-unit extra codegeneracy retracts the zeroth coface. -/
@[stacks 0FKS "split-unit extra codegeneracy and zeroth coface"]
theorem δ₀_comp_s (n : ℕ) :
    ((cosimplicialResolution.eval T).obj X).right.δ 0 ≫ codegeneracy h n =
      𝟙 _ := sorry

/-- Split-unit extra codegeneracies commute with all positive cofaces. -/
@[stacks 0FKS "split-unit extra codegeneracy and cofaces"]
theorem δ_comp_s (n : ℕ) (i : Fin (n + 2)) :
    ((cosimplicialResolution.eval T).obj X).right.δ i.succ ≫
        codegeneracy h (n + 1) =
      codegeneracy h n ≫
        ((cosimplicialResolution.eval T).obj X).right.δ i := sorry

/-- Split-unit extra codegeneracies commute with all positive codegeneracies. -/
@[stacks 0FKS "split-unit extra codegeneracy and codegeneracies"]
theorem σ_comp_s (n : ℕ) (i : Fin (n + 1)) :
    ((cosimplicialResolution.eval T).obj X).right.σ i.succ ≫ codegeneracy h n =
      codegeneracy h (n + 1) ≫
        ((cosimplicialResolution.eval T).obj X).right.σ i := sorry

/-- A split monad unit equips the evaluated canonical resolution with an extra
codegeneracy. -/
@[stacks 0FKS "extra codegeneracy from a split monad unit"]
noncomputable def extraCodegeneracy :
    CosimplicialObject.Augmented.ExtraCodegeneracy
      ((cosimplicialResolution.eval T).obj X) where
  s' := zeroRetraction h
  s := codegeneracy h
  η_comp_s' := η_comp_s' h
  δ₁_comp_s₀ := δ₁_comp_s₀ h
  δ₀_comp_s := δ₀_comp_s h
  δ_comp_s := δ_comp_s h
  σ_comp_s := σ_comp_s h

/-- The retraction stored by the split-unit extra codegeneracy is the chosen unit
retraction. -/
@[simp, stacks 0FKS "retraction of the split-unit extra codegeneracy"]
theorem extraCodegeneracy.s' : (extraCodegeneracy h).s' = h.retraction := sorry

/-- The degreewise maps stored by the split-unit extra codegeneracy are the iterated chosen
retractions. -/
@[simp, stacks 0FKS "maps of the split-unit extra codegeneracy"]
theorem extraCodegeneracy.s (n : ℕ) :
    (extraCodegeneracy h).s n = codegeneracy h n := sorry

end splitUnit

/-- A monad algebra supplies the canonical extra codegeneracy on the resolution of its
underlying object. -/
@[stacks 0FKS "extra codegeneracy on a monad algebra resolution"]
noncomputable def extraCodegeneracy (A : Algebra T) :
    CosimplicialObject.Augmented.ExtraCodegeneracy
      ((cosimplicialResolution.eval T).obj A.A) :=
  splitUnit.extraCodegeneracy A.unitSplitMono

/-- The algebra extra codegeneracy is obtained solely from the algebra's split unit. -/
@[stacks 0FKS "algebra extra codegeneracy as a split-unit construction"]
theorem extraCodegeneracy.eq_splitUnit (A : Algebra T) :
    extraCodegeneracy A = splitUnit.extraCodegeneracy A.unitSplitMono := sorry

/-- The retraction stored by the algebra extra codegeneracy is the algebra structure map. -/
@[simp, stacks 0FKS "retraction of the algebra extra codegeneracy"]
theorem extraCodegeneracy.s' (A : Algebra T) : (extraCodegeneracy A).s' = A.a := sorry

/-- The degreewise maps stored by the algebra extra codegeneracy separate the leading monad
factor and apply the remaining iterate to the algebra structure map. -/
@[simp, stacks 0FKS "maps of the algebra extra codegeneracy"]
theorem extraCodegeneracy.s (A : Algebra T) (n : ℕ) :
    (extraCodegeneracy A).s n =
      (IteratedEndofunctor.prependIso T.toFunctor n).inv.app A.A ≫
        (T.toFunctor ⁺⦋n⦌).map A.a := sorry

end cosimplicialResolution.eval

end CategoryTheory.Monad
