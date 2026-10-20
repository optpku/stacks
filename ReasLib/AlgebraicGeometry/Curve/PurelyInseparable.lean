module

public import Mathlib.CategoryTheory.ComposableArrows.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.RingHom.PurelyInseparable
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Birational.FunctionFieldDegree
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Curve.Nonconstant
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Regular
public import ReasLib.FieldTheory.PurelyInseparable.FiniteTower

@[expose] public section

open AlgebraicGeometry CategoryTheory
open Scheme.Hom
open Scheme.Hom.IsNonconstant

universe u

namespace AlgebraicGeometry.Curve

/-- A purely inseparable function-field extension of proper regular curves factors
through a finite chain of degree-`p` purely inseparable morphisms. -/
theorem existsDegreePFactorization
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (X Y : SchemeOverField k) [Curve X] [Curve Y]
    [Scheme.Regular X.left] [Scheme.Regular Y.left]
    [IsProper X.hom] [IsProper Y.hom]
    (f : X ⟶ Y) (hf : f.left.IsNonconstant)
    (h_pi : (f.left.functionFieldMap
      (@map_genericPoint_eq_of_isDominant _ _ f.left
        inferInstance inferInstance (isDominant_of_curves hf))).IsPurelyInseparable) :
    ∃ (n : ℕ) (D : ComposableArrows (SchemeOverField k) n)
      (h_curve : ∀ i, Curve (D.obj i))
      (h_regular : ∀ i, Scheme.Regular (D.obj i).left)
      (h_proper : ∀ i, IsProper (D.obj i).hom)
      (h_nonconstant : ∀ i : Fin n, (D.map' i.1 (i.1 + 1)).left.IsNonconstant),
      ∃ (eX : X ≅ D.left) (eY : D.right ≅ Y),
        eX.hom ≫ D.hom ≫ eY.hom = f ∧
          ∀ i : Fin n,
            let g := D.map' i.1 (i.1 + 1)
            let h_source := h_curve i.castSucc
            let h_target := h_curve i.succ
            let h_dominant : IsDominant g.left :=
              @isDominant_of_curves k _ _ _
                h_source h_target g (h_nonconstant i)
            @inducedFunctionFieldDegree _ _ g.left
                h_source.toVariety.toIsIntegral h_target.toVariety.toIsIntegral h_dominant = p ∧
              ¬@Algebra.IsSeparable
                (D.obj i.succ).left.functionField
                (D.obj i.castSucc).left.functionField inferInstance inferInstance
                (@functionFieldAlgebra _ _ g.left
                  h_source.toVariety.toIsIntegral h_target.toVariety.toIsIntegral
                  (@map_genericPoint_eq_of_isDominant _ _ g.left
                    h_source.toVariety.toIsIntegral h_target.toVariety.toIsIntegral
                    h_dominant)) := sorry

end AlgebraicGeometry.Curve
