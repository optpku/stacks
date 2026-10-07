module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.OpenImmersion
import StacksCheckRecall

/-!
# Lemma 29.35.7

Any open immersion is G-unramified.

@stack 02GB
-/

@[expose] public section

open AlgebraicGeometry

universe u

/- Lemma 29.35.7: Any open immersion is G-unramified. -/
@[stacks 02GB] #check (AlgebraicGeometry.instGUnramifiedOfIsOpenImmersion :
  ∀ {X Y : Scheme.{u}} {f : X ⟶ Y} [IsOpenImmersion f], GUnramified f)
