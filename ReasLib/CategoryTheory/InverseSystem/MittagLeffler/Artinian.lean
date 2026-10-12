/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Subobject
public import Mathlib.RingTheory.Artinian.Module
public import ReasLib.CategoryTheory.InverseSystem.MittagLeffler
public import ReasLib.CategoryTheory.Filtered.EssentiallyConstant.Presentation

@[expose] public section

open CategoryTheory Opposite

universe u

namespace CategoryTheory.SequentialInverseSystem.IsMittagLeffler

/-- A sequential inverse system of Artinian modules satisfies the Mittag-Leffler condition. -/
theorem of_isArtinian {A : Type u} [Ring A]
    (F : SequentialInverseSystem (ModuleCat.{u} A))
    [∀ n : ℕ, IsArtinian A (F.obj (op n))] :
    F.IsMittagLeffler := sorry

end CategoryTheory.SequentialInverseSystem.IsMittagLeffler

namespace CategoryTheory.Limits.Cone.IsEssentiallyConstant

/-- A limit cone on a Mittag-Leffler sequential inverse system of modules is essentially
constant when its vertex is Artinian. -/
theorem of_isMittagLeffler_of_isArtinian
    {A : Type u} [Ring A] (F : SequentialInverseSystem (ModuleCat.{u} A))
    (c : Cone F) [IsArtinian A c.pt]
    (hF : F.IsMittagLeffler) (hc : IsLimit c) :
    c.IsEssentiallyConstant := sorry

end CategoryTheory.Limits.Cone.IsEssentiallyConstant
