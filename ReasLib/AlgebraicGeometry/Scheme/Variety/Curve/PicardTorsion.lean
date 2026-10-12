/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Data.ZMod.Basic
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Over
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Point
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.ArithmeticGenus

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Curve

/-- A genus-one smooth proper curve with constant global functions acquires a rational point
over a finite separable extension whose prime-to-characteristic Picard torsion is free of rank
two over `ZMod n`. -/
theorem existsPicardTorsionGenusOne
    {k : Type u} [Field k] (X : SchemeOverField k) [Curve X] [IsProper X.hom]
    [Smooth X.hom] (n g : ℕ) (h_n_pos : 1 ≤ n)
    (h_unit : IsUnit (n : k))
    (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_genus : g = SchemeOverField.genus X
      (AlgebraicGeometry.topologicalKrullDim_eq_one X) hΓ)
    (h_g : g = 1) :
    ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k')
      (_ : FiniteDimensional k k') (_ : Algebra.IsSeparable k k'),
      ∃ x : SchemeOverField.point k' ⟶ FieldExtension.Over.baseChange k k' X,
        Nonempty
          (AddSubgroup.torsionBy
              (FieldExtension.Over.baseChange k k' X).left.PicardGroup (n : ℤ) ≃+
            (Fin 2 → ZMod n)) := sorry

/-- A smooth proper curve of genus at least two with constant global functions acquires a
rational point over a finite separable extension with bounded degree and full prime-to-
characteristic Picard torsion. -/
theorem existsPicardTorsionGenusGeTwo
    {k : Type u} [Field k] (X : SchemeOverField k) [Curve X] [IsProper X.hom]
    [Smooth X.hom] (n g : ℕ) (h_n_pos : 1 ≤ n)
    (h_unit : IsUnit (n : k))
    (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_genus : g = SchemeOverField.genus X
      (AlgebraicGeometry.topologicalKrullDim_eq_one X) hΓ)
    (h_g : 2 ≤ g) :
    ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k')
      (_ : FiniteDimensional k k') (_ : Algebra.IsSeparable k k'),
      ∃ x : SchemeOverField.point k' ⟶ FieldExtension.Over.baseChange k k' X,
        Module.finrank k k' ≤ (2 * g - 2) * Nat.factorial (n ^ (2 * g)) ∧
        Nonempty
          (AddSubgroup.torsionBy
              (FieldExtension.Over.baseChange k k' X).left.PicardGroup (n : ℤ) ≃+
            (Fin (2 * g) → ZMod n)) := sorry

end AlgebraicGeometry.Curve
