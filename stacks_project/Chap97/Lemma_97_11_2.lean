module

public import stacks_project.Chap97.Lemma_97_11_2_Comparison
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.RestrictionOfScalars

universe u

/- Lemma 97.11.2: for morphisms `X ⟶ Z ⟶ B` and `B' ⟶ B` of algebraic spaces over a
scheme `S`, with `Z' = B' ×_B Z` and `X' = B' ×_B X`, the fppf sheaves on `Sch/S`
satisfy `Res_{Z'/B'}(X') ≅ B' ×_B Res_{Z/B}(X)`. -/
@[stacks 05YC]
#check (RestrictionOfScalars.pullbackIso :
    ∀ {S : Scheme.{u}} {X Z B B' : AlgebraicSpace S} (f : X ⟶ Z) (g : Z ⟶ B)
      (h : B' ⟶ B),
      restrictionOfScalarsSheaf (mapX f g h) (pullback.fst h g) ≅
        pullback (uliftSheafMap h) (toUliftSheaf f g))
