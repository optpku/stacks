module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Basic
public import stacks_project.Chap98.Definition_98_13_1_Versal
import Mathlib.Tactic.CrossRefAttribute

/-!
# Smoothness at a finite type point versus versality of the slice object

For a morphism of schemes locally of finite type over a locally Noetherian
base, smoothness at a finite type point is equivalent to versality of the
morphism viewed as an object of `(Sch/V)_fppf` over `U`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- The object of `(Sch/V)_fppf` over `U` associated to a morphism `f : U ⟶ V`
of schemes over `S`. -/
def sliceHomObject {S U V : Scheme.{u}} (hU : U ⟶ S) (hV : V ⟶ S)
    (f : U ⟶ V) (h_over : f ≫ hV = hU) :
    (GroupoidsOver.slice (Over.mk hV)).total :=
  Over.mk (Over.homMk f h_over : Over.mk hU ⟶ Over.mk hV)

/-- The slice object of `f` lies over `U ⟶ S`. -/
theorem sliceHomObject_over {S U V : Scheme.{u}} (hU : U ⟶ S) (hV : V ⟶ S)
    (f : U ⟶ V) (h_over : f ≫ hV = hU) :
    (GroupoidsOver.slice (Over.mk hV)).p.obj (sliceHomObject hU hV f h_over) =
      Over.mk hU :=
  sorry

/-- `sliceHomObject hU hV f h_over` is the over-object associated to `f`. -/
theorem sliceHomObject_spec {S U V : Scheme.{u}} (hU : U ⟶ S) (hV : V ⟶ S)
    (f : U ⟶ V) (h_over : f ≫ hV = hU) :
    sliceHomObject hU hV f h_over =
      Over.mk (Over.homMk f h_over : Over.mk hU ⟶ Over.mk hV) :=
  sorry

/-- Lemma 98.12.4: for a locally Noetherian scheme `S`, a morphism `f : U ⟶ V`
of schemes locally of finite type over `S`, and a finite type point `u0` of `U`,
`f` is smooth at `u0` if and only if `f`, viewed as an object of `(Sch/V)_fppf`
over `U`, is versal at `u0`. -/
@[stacks 0CXL]
theorem smoothAt_iff_isVersalAt {S U V : Scheme.{u}} [IsLocallyNoetherian S]
    (hU : U ⟶ S) (hV : V ⟶ S) [LocallyOfFiniteType hU] [LocallyOfFiniteType hV]
    (f : U ⟶ V) (h_over : f ≫ hV = hU) (u0 : U) [IsFiniteTypePoint u0] :
    f.SmoothAt u0 ↔
      IsVersalAt hU (sliceHomObject hU hV f h_over)
        (sliceHomObject_over hU hV f h_over) u0 :=
  sorry

end AlgebraicGeometry.GroupoidsOver
