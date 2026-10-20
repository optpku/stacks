module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.VersalAt.Smooth
import StacksCheckRecall

/-!
# Smoothness at a finite type point versus versality of the slice object

For a morphism of schemes locally of finite type over a locally Noetherian
base, smoothness at a finite type point is equivalent to versality of the
morphism viewed as an object of `(Sch/V)_fppf` over `U`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.GroupoidsOver

/- Lemma 98.12.4: for a locally Noetherian scheme `S`, a morphism `f : U ⟶ V`
of schemes locally of finite type over `S`, and a finite type point `u0` of `U`,
`f` is smooth at `u0` if and only if `f`, viewed as an object of `(Sch/V)_fppf`
over `U`, is versal at `u0`. -/
@[stacks 0CXL] #check
  (AlgebraicGeometry.GroupoidsOver.smoothAt_iff_isVersalAt :
    ∀ {S U V : Scheme.{u}} [IsLocallyNoetherian S]
    (hU : U ⟶ S) (hV : V ⟶ S) [LocallyOfFiniteType hU] [LocallyOfFiniteType hV]
    (f : U ⟶ V) (h_over : f ≫ hV = hU) (u0 : U) [IsFiniteTypePoint u0],
    f.SmoothAt u0 ↔
      IsVersalAt hU (sliceHomObject hU hV f h_over)
        (sliceHomObject_over hU hV f h_over) u0)

end AlgebraicGeometry.GroupoidsOver
