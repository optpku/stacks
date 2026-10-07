module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.LocallyQuasiFinite.MaximalLocus

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.LocallyQuasiFinite

/- Lemma 37.74.7 (1): if the geometric fibre-component count of a separated,
locally quasi-finite, universally open morphism attains the finite maximum `d`,
then its `d`-level set is open. -/
@[stacks 0F37] #check
  (AlgebraicGeometry.LocallyQuasiFinite.isOpen_geometricFiberComponentCount_eq_of_isGreatest :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [LocallyQuasiFinite f]
      [IsSeparated f] [UniversallyOpen f] (d : ℕ)
      (hd : IsGreatest (Set.range f.geometricFiberComponentCount) d),
      IsOpen {y : Y | f.geometricFiberComponentCount y = d})

#check
  (AlgebraicGeometry.LocallyQuasiFinite.maximalFiberComponentCountLocus :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [LocallyQuasiFinite f]
      [IsSeparated f] [UniversallyOpen f] (d : ℕ)
      (hd : IsGreatest (Set.range f.geometricFiberComponentCount) d),
      Y.Opens)

#check
  (AlgebraicGeometry.LocallyQuasiFinite.mem_maximalFiberComponentCountLocus :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [LocallyQuasiFinite f]
      [IsSeparated f] [UniversallyOpen f] (d : ℕ)
      (hd : IsGreatest (Set.range f.geometricFiberComponentCount) d) (y : Y),
      y ∈ AlgebraicGeometry.LocallyQuasiFinite.maximalFiberComponentCountLocus f d hd ↔
        f.geometricFiberComponentCount y = d)

/- Lemma 37.74.7 (2): over the open locus where the finite maximum of the
geometric fibre-component count is attained, the restricted morphism is finite. -/
@[stacks 0F37] #check
  (AlgebraicGeometry.LocallyQuasiFinite.instIsFiniteMaximalFiberComponentCountLocus :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [LocallyQuasiFinite f]
      [IsSeparated f] [UniversallyOpen f] (d : ℕ)
      (hd : IsGreatest (Set.range f.geometricFiberComponentCount) d),
      IsFinite
        (f ∣_ AlgebraicGeometry.LocallyQuasiFinite.maximalFiberComponentCountLocus f d hd))

end AlgebraicGeometry.LocallyQuasiFinite
