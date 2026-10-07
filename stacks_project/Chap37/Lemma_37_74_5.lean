module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.LocallyQuasiFinite

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.LocallyQuasiFinite

/- Lemma 37.74.5 (1): for a locally quasi-finite morphism, the geometric
irreducible- and connected-component count functions agree. -/
@[stacks 0F35] #check
  (AlgebraicGeometry.LocallyQuasiFinite.geometricComponentCounts_eq :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [LocallyQuasiFinite f],
      f.geometricIrreducibleFiberComponentCount = f.geometricFiberComponentCount)

/- A locally quasi-finite morphism with quasi-compact source has a finite
uniform upper bound for its geometric fibre-component count. -/
#check
  (AlgebraicGeometry.LocallyQuasiFinite.exists_geometricFiberComponentCount_le :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [LocallyQuasiFinite f]
      [CompactSpace X],
      ∃ d : ℕ, ∀ y : Y, f.geometricFiberComponentCount y ≤ d)

/- Lemma 37.74.5 (2): if the source is quasi-compact and the target is
inhabited, the common geometric fibre-component count attains a finite maximum. -/
@[stacks 0F35] #check
  (AlgebraicGeometry.LocallyQuasiFinite.exists_isGreatest_geometricFiberComponentCount :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [LocallyQuasiFinite f]
      [CompactSpace X] [Nonempty Y],
      ∃ d : ℕ, IsGreatest (Set.range f.geometricFiberComponentCount) d)

end AlgebraicGeometry.LocallyQuasiFinite
