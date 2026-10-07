module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Pullbacks
public import ReasLib.AlgebraicGeometry.Scheme.TorIndependence.Affine
public import ReasLib.Algebra.Category.ModuleCat.Tor.Independence.BaseChange

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.TorIndependentOver

/-- Flat base change preserves Tor independence of two schemes over a common base. -/
theorem pullback {S S' : Scheme.{u}} {X Y : Over S} (h : TorIndependentOver X Y)
    (f : S' ⟶ S) [Flat f] :
    TorIndependentOver ((Over.pullback f).obj X) ((Over.pullback f).obj Y) := sorry

/-- In a commutative square of schemes, flatness of the right morphism and the
left morphism implies Tor independence of the base-changed product and the
upper-left scheme over the original product. -/
theorem baseChangeProduct_of_flat
    {Z' Y' X' S' S : Scheme.{u}}
    (i : Z' ⟶ Y') (g : Z' ⟶ X') (q : Y' ⟶ S') (p : X' ⟶ S') (s : S ⟶ S')
    [Flat q] [Flat g] (sq : CommSq i g q p) :
    TorIndependentOver
      (Over.mk
        (pullback.map (pullback.snd p s) (pullback.snd q s) p q
          (pullback.fst p s) (pullback.fst q s) s
          pullback.condition.symm pullback.condition.symm))
      (Over.mk (pullback.lift g i sq.w.symm)) := sorry

end AlgebraicGeometry.Scheme.TorIndependentOver
