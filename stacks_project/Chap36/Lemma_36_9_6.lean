module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Koszul.PrincipalOpen.Factorization
public import stacks_project.Chap36.Proposition_36_9_5
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open KoszulComplex.PowerTower

universe u

namespace AlgebraicGeometry
namespace RingedSpace
namespace ModuleDerived
namespace Koszul

/- Lemma 36.9.6: let `X = Spec(A)` and let
`U = Scheme.PrincipalOpenCech.openSubset f`. If the restrictions to `U` of the homology
sheaves of `E : Scheme.DerivedQCoh X` vanish in degrees `-r + 1, …, 0`, then every
degree-zero global section `s : affineUnitDerived A ⟶ E.obj` factors through a powered
Koszul object. Here `derivedStage f e` is the source's `K_(e + 1)`, since the tower is
indexed from zero. -/
@[stacks 08E3] #check
  (AlgebraicGeometry.RingedSpace.ModuleDerived.Koszul.exists_poweredStage_lift :
    ∀ {A : Type u} [CommRing A] {r : ℕ}
        (f : Fin r → A) (E : Scheme.DerivedQCoh (Spec (CommRingCat.of A))),
      (∀ i : ℤ, -(r : ℤ) + 1 ≤ i → i ≤ 0 →
        IsZero
          ((moduleRestrictionToOpen (Spec (CommRingCat.of A)).toRingedSpace
            (Scheme.PrincipalOpenCech.openSubset f)).obj
              ((DerivedCategory.homologyFunctor
                (Spec (CommRingCat.of A)).toRingedSpace.Modules i).obj E.obj))) →
      ∀ s : affineUnitDerived A ⟶ E.obj,
        ∃ e : ℕ,
          ∃ g : (affineDerivedTilde A).obj (derivedStage f e) ⟶ E.obj,
            ((affineDerivedTilde A).map
              (DerivedCategory.Q.map (Fin.unitComponent f e)) :
                affineUnitDerived A ⟶ (affineDerivedTilde A).obj (derivedStage f e)) ≫ g = s)

end Koszul
end ModuleDerived
end RingedSpace
end AlgebraicGeometry

end
