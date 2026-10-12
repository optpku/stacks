/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.ObjectProperty.WeakSerre
public import ReasLib.CategoryTheory.Sites.AbelianSheaf
public import Mathlib.GroupTheory.Torsion
import Mathlib.Tactic.CrossRefAttribute

/-!
# Torsion Abelian Sheaves

An abelian sheaf is torsion when every section is locally of finite additive order.  The
locality is essential: no uniform order, and not even torsion of the whole section group, is
required before passing to a cover.
-/

@[expose] public section

open CategoryTheory Opposite
open CategoryTheory.ObjectProperty

noncomputable section

universe w v u

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- A sheaf of abelian groups is locally torsion if every section restricts, along some cover,
to sections of finite additive order. -/
@[stacks 0DD7 "locally torsion abelian sheaf"]
def IsLocallyTorsion (F : Sheaf J AddCommGrpCat.{w}) : Prop :=
  ∀ (U : C) (s : F.obj.obj (op U)),
    ∃ T : J.Cover U, ∀ I : T.Arrow,
      IsOfFinAddOrder (F.obj.map I.f.op s)

namespace IsLocallyTorsion

/-- Sectionwise torsion implies local torsion. -/
theorem ofSectionwise {F : Sheaf J AddCommGrpCat.{w}}
    (hF : ∀ (U : C) (s : F.obj.obj (op U)), IsOfFinAddOrder s) :
    F.IsLocallyTorsion := sorry

end IsLocallyTorsion

/-- The object property of locally torsion abelian sheaves on a site. -/
@[stacks 0DD7 "torsion abelian sheaf object property"]
def torsion (J : GrothendieckTopology C) :
    ObjectProperty (SiteAbelianSheafCat J) :=
  IsLocallyTorsion

namespace Torsion

/-- Membership in `torsion J` is the local finite-order condition on sections. -/
@[simp]
theorem mem_iff (F : SiteAbelianSheafCat J) :
    torsion J F ↔ F.IsLocallyTorsion := sorry

variable [HasSheafify J AddCommGrpCat.{max u v}]

/-- Torsion abelian sheaves form a Serre class. -/
@[stacks 0DD7 "torsion abelian sheaves form a Serre class", instance]
theorem isSerre : (torsion J).IsSerreClass := sorry

end Torsion

end CategoryTheory.Sheaf
