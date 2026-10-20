module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Pushforward.Perfect
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived

/- Lemma 36.27.4: for a flat proper morphism `f : X ⟶ S` with `S` Noetherian,
the derived pushforward of every perfect object of `D(𝒪_X)` is perfect in `D(𝒪_S)`. -/
@[stacks 0B6F] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.pushforward_isPerfect_of_flat_of_proper :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S] [Flat f] [IsProper f]
      (E : RingedSpace.ModuleDerived X.toRingedSpace),
      RingedSpace.ModuleDerived.IsPerfect E →
        RingedSpace.ModuleDerived.IsPerfect
          ((RingedSpace.moduleDerivedPushforward f.toShHom).obj E))

end AlgebraicGeometry.Scheme.ModuleDerived
