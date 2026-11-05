module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pullback.Composition
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pullback.Differentials
import Mathlib.Tactic.CrossRefAttribute

/-!
# Composition of pullback comparisons for relative differentials

The comparison attached to a pasted pair of commutative squares is the composite of the two
individual comparisons after the canonical identification of pullback along a composite with
iterated pullback.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Hom.Differentials

variable {X X' X'' S S' S'' : RingedSpace.{u}}
variable {f : X' ⟶ X} {f' : X'' ⟶ X'} {s : S' ⟶ S} {s' : S'' ⟶ S'}
variable {h : X ⟶ S} {h' : X' ⟶ S'} {h'' : X'' ⟶ S''}

/-- The iterated comparison associated to two composable commutative squares, transported to
the pullback along their composite. -/
@[stacks 01UW "iterated comparison morphism"]
noncomputable def comparisonComp
    (sq : CommSq f h' h s) (sq' : CommSq f' h'' h' s') :
    (RingedSpace.Hom.pullback (f' ≫ f)).obj Ω[h] ⟶ Ω[h''] :=
  (RingedSpace.Hom.pullbackCompIso f' f).hom.app Ω[h] ≫
    (RingedSpace.Hom.pullback f').map (comparison sq) ≫
    comparison sq'

/-- Pullback comparison morphisms for relative differentials are compatible with composition
of commutative squares. -/
@[stacks 01UW]
theorem comparison_comp
    (sq : CommSq f h' h s) (sq' : CommSq f' h'' h' s') :
    comparison (CommSq.horiz_comp sq' sq) =
      comparisonComp sq sq' := sorry

end AlgebraicGeometry.RingedSpace.Hom.Differentials
