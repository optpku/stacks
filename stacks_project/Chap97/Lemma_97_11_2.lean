module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RestrictionOfScalars.BaseChange
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
#check (AlgebraicGeometry.AlgebraicSpace.RestrictionOfScalars.pullbackIso :
    ∀ {S : Scheme.{u}} {X Z B B' : AlgebraicSpace S} (f : X ⟶ Z) (g : Z ⟶ B)
      (h : B' ⟶ B),
      AlgebraicGeometry.AlgebraicSpace.RestrictionOfScalars.sheaf
        (AlgebraicGeometry.AlgebraicSpace.RestrictionOfScalars.mapX f g h) (pullback.fst h g) ≅
        pullback (AlgebraicGeometry.AlgebraicSpace.toSheaf.map h)
          (AlgebraicGeometry.AlgebraicSpace.RestrictionOfScalars.toBase f g))
