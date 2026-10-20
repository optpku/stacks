/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.TensorPower
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ExceptionalCurve.Picard

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.IsExceptionalCurveFirstKind

/-- The module on the target obtained by twisting a representative by its exceptional-curve
degree and then pushing it forward along the contraction. -/
noncomputable def descendedModule
    {X X' : Scheme.{u}} [IsNoetherian X]
    (E : X.IdealSheafData) [IsExceptionalCurveFirstKind E]
    (b : X ⟶ X') (x : closedPoints X') (hb : IsContraction E b x)
    (a : X.PicardGroup) : X'.Modules :=
  (Scheme.Modules.pushforward b).obj
    (Scheme.Modules.twistByTensorPower E.associatedSheaf
      (Scheme.PicardGroup.repr a) (degree E a))

/-- The module descended from a Picard class along a contraction is invertible. -/
theorem descendedModule_invertible
    {X X' : Scheme.{u}} [IsNoetherian X]
    (E : X.IdealSheafData) [IsExceptionalCurveFirstKind E]
    (b : X ⟶ X') (x : closedPoints X') (hb : IsContraction E b x)
    (a : X.PicardGroup) : Scheme.Modules.Invertible (descendedModule E b x hb a) := sorry

/-- An exceptional-curve contraction identifies the source Picard group with the target
Picard group together with the integer degree along the exceptional curve. -/
noncomputable def picardDecomposition
    {X X' : Scheme.{u}} [IsNoetherian X]
    (E : X.IdealSheafData) [IsExceptionalCurveFirstKind E]
    (b : X ⟶ X') (x : closedPoints X') (hb : IsContraction E b x) :
    X.PicardGroup ≃+ X'.PicardGroup × ℤ where
  toFun a :=
    (@Scheme.Modules.picardClass X' (descendedModule E b x hb a)
      (descendedModule_invertible E b x hb a), degree E a)
  invFun p := Scheme.Hom.picardPullback b p.1 + exceptionalTwist E p.2
  left_inv := sorry
  right_inv := sorry
  map_add' := sorry

/-- A Picard class has coordinates `(a', n)` under an exceptional-curve contraction exactly
when it is the pullback of `a'` plus the exceptional twist by `n`. -/
theorem picardDecomposition_eq_iff
    {X X' : Scheme.{u}} [IsNoetherian X]
    (E : X.IdealSheafData) [IsExceptionalCurveFirstKind E]
    (b : X ⟶ X') (x : closedPoints X') (hb : IsContraction E b x)
    (a : X.PicardGroup) (a' : X'.PicardGroup) (n : ℤ) :
    picardDecomposition E b x hb a = (a', n) ↔
      a = Scheme.Hom.picardPullback b a' + exceptionalTwist E n := sorry

/-- The additive homomorphism given by the first Picard coordinate of an exceptional-curve
contraction. -/
noncomputable def picardDescent
    {X X' : Scheme.{u}} [IsNoetherian X]
    (E : X.IdealSheafData) [IsExceptionalCurveFirstKind E]
    (b : X ⟶ X') (x : closedPoints X') (hb : IsContraction E b x) :
    X.PicardGroup →+ X'.PicardGroup :=
  (AddMonoidHom.fst X'.PicardGroup ℤ).comp (picardDecomposition E b x hb).toAddMonoidHom

/-- The representative of the first Picard coordinate is the pushforward of the
exceptionally twisted representative on the source. -/
noncomputable def picardDescent_reprIso
    {X X' : Scheme.{u}} [IsNoetherian X]
    (E : X.IdealSheafData) [IsExceptionalCurveFirstKind E]
    (b : X ⟶ X') (x : closedPoints X') (hb : IsContraction E b x)
    (a : X.PicardGroup) :
    Scheme.PicardGroup.repr (picardDescent E b x hb a) ≅
      (Scheme.Modules.pushforward b).obj
        (Scheme.Modules.twistByTensorPower E.associatedSheaf
          (Scheme.PicardGroup.repr a) (degree E a)) :=
  @Scheme.PicardGroup.reprPicardClassIso X' (descendedModule E b x hb a)
    (descendedModule_invertible E b x hb a)

end AlgebraicGeometry.IsExceptionalCurveFirstKind
