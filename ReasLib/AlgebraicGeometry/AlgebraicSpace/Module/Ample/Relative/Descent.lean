/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Ample.Relative
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Fpqc
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Monoidal

/-!
# Fpqc descent of relatively ample modules on algebraic spaces

Relative ampleness of an invertible module on a morphism of algebraic spaces is
equivalent to relative ampleness of every pullback along an fpqc covering of the
target.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicSpace CategoryTheory Limits MonoidalCategory

universe u v

namespace AlgebraicGeometry.AlgebraicSpace.RelativelyAmple

/-- An invertible module on a morphism of algebraic spaces is relatively ample if and
only if each of its canonical base changes along an fpqc covering family of the target
is relatively ample. -/
theorem iff_forall_baseChange_of_fpqcCovering
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (L : X.Modules)
    [isInvertibleObject L] {ι : Type v} (family : ι → Over Y)
    (hfamily : FpqcCovering family) :
    RelativelyAmple f L ↔
      ∀ i, RelativelyAmple (pullback.snd f (family i).hom)
        ((Modules.pullback (pullback.fst f (family i).hom)).obj L) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.RelativelyAmple
