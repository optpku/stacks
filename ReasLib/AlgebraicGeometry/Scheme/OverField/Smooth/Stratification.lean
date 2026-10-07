module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import ReasLib.AlgebraicGeometry.Scheme.Algebraic
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Reduced.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Reduced.SmoothLocus
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.OpenComplement

/-!
# Smooth stratifications after purely inseparable extension

This file records a finite smooth stratification of a finite-type scheme after
reduction and a suitable finite purely inseparable extension of the base field.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]

/-- A finite-type scheme over a field admits, after reduction and a finite purely inseparable
extension of the base field, a finite descending filtration by closed subschemes whose successive
locally closed strata are smooth over the extended field. -/
@[stacks 0H3W]
theorem exists_smoothStratification
    (X : SchemeOverField k) [Algebraic X] :
    ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k')
      (_ : FiniteDimensional k k') (_ : IsPurelyInseparable k k'),
      let Y := FieldExtension.Reduced.baseChange k k' X
      ∃ t : ℕ, ∃ Z : Fin (t + 1) → Y.left.IdealSheafData,
        Z 0 = ⊥ ∧
        Z (Fin.last t) = ⊤ ∧
        (∀ i : Fin t, Z i.castSucc ≤ Z i.succ) ∧
        ∀ i : Fin t,
          Smooth
            (((Z i.succ).comap (Z i.castSucc).subschemeι).openComplement.ι ≫
              (Z i.castSucc).subschemeι ≫ Y.hom) := sorry

end AlgebraicGeometry.SchemeOverField
