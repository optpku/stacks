/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.Ring.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Diagrams of square-zero extensions of ring sheaves

An extension row specifies a ring projection and an additive inclusion of a module over
the quotient. Compatible rows specify both vertical ring maps and the prescribed module map.
All sheaves and maps are explicit; the predicates impose conditions on this data.
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace SheafOfModules.RingedSite.SquareZeroExtension

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]

/-- A projection and an additive inclusion form a square-zero extension row when the
projection is locally surjective, its section kernel ideals are square zero, the additive
row is short exact, and the inclusion respects the quotient-module action. -/
def IsExtensionRow {middle quotient : Sheaf J CommRingCat.{w}}
    (proj : middle ⟶ quotient) (M : SheafOfModules.{w} (Sheaf.ringSheafOfComm quotient))
    (inclusion : (SheafOfModules.toSheaf (Sheaf.ringSheafOfComm quotient)).obj M ⟶
      (sheafCompose J (forget₂ RingCat.{w} AddCommGrpCat.{w})).obj
        (Sheaf.ringSheafOfComm middle)) : Prop :=
  Sheaf.IsLocallySurjective proj ∧
    (∀ U : Cᵒᵖ, RingHom.ker (proj.hom.app U).hom ^ 2 = ⊥) ∧
    (∃ hzero : inclusion ≫
        (sheafCompose J (forget₂ RingCat.{w} AddCommGrpCat.{w})).map
          (Sheaf.ringSheafOfCommMap proj) = 0,
      (ShortComplex.mk inclusion
        ((sheafCompose J (forget₂ RingCat.{w} AddCommGrpCat.{w})).map
          (Sheaf.ringSheafOfCommMap proj)) hzero).ShortExact) ∧
    ∀ (U : Cᵒᵖ) (a : middle.obj.obj U) (m : M.val.obj U),
      inclusion.hom.app U ((proj.hom.app U a) • m) =
        Mul.mul (α := middle.obj.obj U) a (inclusion.hom.app U m)

/-- Two explicit square-zero extension rows form a compatible diagram when the vertical
ring maps commute with the projections and induce the prescribed quotient-linear module
map on the chosen kernel inclusions. -/
def IsSolution {A' A : Sheaf J CommRingCat.{w}} (π : A' ⟶ A)
    (M : SheafOfModules.{w} (Sheaf.ringSheafOfComm A))
    (j : (SheafOfModules.toSheaf (Sheaf.ringSheafOfComm A)).obj M ⟶
      (sheafCompose J (forget₂ RingCat.{w} AddCommGrpCat.{w})).obj
        (Sheaf.ringSheafOfComm A'))
    {O : Sheaf J CommRingCat.{w}} (fSharp : A ⟶ O)
    (G : SheafOfModules.{w} (Sheaf.ringSheafOfComm O))
    (c : M ⟶ (SheafOfModules.restrictScalars (Sheaf.ringSheafOfCommMap fSharp)).obj G)
    (middle : Sheaf J CommRingCat.{w}) (proj : middle ⟶ O)
    (i : (SheafOfModules.toSheaf (Sheaf.ringSheafOfComm O)).obj G ⟶
      (sheafCompose J (forget₂ RingCat.{w} AddCommGrpCat.{w})).obj
        (Sheaf.ringSheafOfComm middle))
    (structureMap : A' ⟶ middle) : Prop :=
  IsExtensionRow π M j ∧ IsExtensionRow proj G i ∧
    structureMap ≫ proj = π ≫ fSharp ∧
    ∀ (U : Cᵒᵖ) (m : M.val.obj U),
      structureMap.hom.app U (j.hom.app U m) = i.hom.app U (c.val.app U m)

end SheafOfModules.RingedSite.SquareZeroExtension
