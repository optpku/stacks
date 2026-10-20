module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.SchemeTheoreticImage.Reduced
import StacksCheckRecall

/-!
# Lemma 29.6.7

The scheme-theoretic image of a reduced scheme is the reduced induced structure on the closure
of its set-theoretic range.

@stack 056B
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

#check (AlgebraicGeometry.Scheme.Hom.ker_eq_vanishingIdeal_closure_range_of_isReduced :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsReduced X],
    f.ker = Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure (Set.range f)))

/- Lemma 29.6.7: The scheme-theoretic image of a morphism from a reduced scheme is the
reduced induced scheme structure on the closure of its set-theoretic range. -/
@[stacks 056B] #check
  (AlgebraicGeometry.Scheme.Hom.image_eq_vanishingIdeal_subscheme_closure_range_of_isReduced :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsReduced X],
      f.image = (Scheme.IdealSheafData.vanishingIdeal
        (TopologicalSpace.Closeds.closure (Set.range f))).subscheme)
