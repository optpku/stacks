module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.FlatDescent
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

/-!
# Lemma 31.28.1 canonical check

Flat descent of an invertible module trivial on the generic fiber is owned by
the scheme-morphism Picard API.
-/

/- Lemma 31.28.1: an invertible module on the source of a flat morphism of
locally Noetherian schemes descends from an integral normal target when every
fiber is integral, the morphism is quasi-compact or locally of finite type,
and the module is trivial on the generic fiber. -/
@[stacks 0BD7] #check
  (AlgebraicGeometry.Scheme.Hom.FlatDescent.existsInvertiblePullback :
    ∀ {X Y : Scheme.{u}} (φ : X ⟶ Y)
      [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsIntegral Y],
      Y.isNormal →
        ∀ [Flat φ],
          (∀ y : Y, IsIntegral (Scheme.Hom.fiber φ y)) →
            (QuasiCompact φ ∨ LocallyOfFiniteType φ) →
              ∀ (L : X.Modules) [Scheme.Modules.Invertible L],
                Nonempty
                    (((Scheme.Modules.pullback
                      (Scheme.Hom.fiberι φ (genericPoint Y))).obj L) ≅
                        (SheafOfModules.unit
                            (Scheme.Hom.fiber φ (genericPoint Y)).ringCatSheaf :
                          (Scheme.Hom.fiber φ (genericPoint Y)).Modules)) →
                  ∃ (N : Y.Modules) (_ : Scheme.Modules.Invertible N),
                    Nonempty (L ≅ (Scheme.Modules.pullback φ).obj N))
