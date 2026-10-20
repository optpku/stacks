module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.VersalAt
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Smoothness at a finite type point and versality

Smoothness of a scheme morphism at a finite type point is equivalent to
versality of its canonical slice object at that point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- For a locally Noetherian scheme `S`, a morphism `f : U ⟶ V` of schemes
locally of finite type over `S` is smooth at a finite type point `u0` of `U`
if and only if its object of `(Sch/V)_fppf` over `U` is versal at `u0`. -/
@[stacks 0CXL]
theorem smoothAt_iff_isVersalAt {S U V : Scheme.{u}} [IsLocallyNoetherian S]
    (hU : U ⟶ S) (hV : V ⟶ S) [LocallyOfFiniteType hU] [LocallyOfFiniteType hV]
    (f : U ⟶ V) (h_over : f ≫ hV = hU) (u0 : U) [IsFiniteTypePoint u0] :
    f.SmoothAt u0 ↔
      IsVersalAt hU (sliceHomObject hU hV f h_over)
        (sliceHomObject_over hU hV f h_over) u0 :=
  sorry

end AlgebraicGeometry.GroupoidsOver
