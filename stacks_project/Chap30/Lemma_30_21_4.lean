module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Relative.Proper
import StacksCheckRecall

/-!
# Relative ampleness near a proper fiber over a Noetherian base

For a proper morphism to a Noetherian scheme, an invertible module that is ample
on one scheme-theoretic fibre is relatively ample over some open neighbourhood
of that point.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.RelativelyAmple

/- Lemma 30.21.4: let `f : X ⟶ Y` be a proper morphism of schemes with `Y` Noetherian,
let `L` be an invertible `𝒪_X`-module, and let `y` be a point of `Y` such that the
pullback of `L` to the scheme-theoretic fibre `X_y` is ample. Then there is an open
neighbourhood `V ⊂ Y` of `y` such that the restriction of `L` to `f ⁻¹ᵁ V` is
relatively ample on `f ∣_ V`. The checked theorem is the source-cited generalization,
Lemma 37.50.3, which does not require Noetherianity and therefore covers this case. -/
@[stacks 0D2N] #check
  (AlgebraicGeometry.RelativelyAmple.exists_morphismRestrict_of_isAmple_fiber :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (L : X.Modules) [L.Invertible] (y : Y)
    [Scheme.Modules.IsAmple ((Scheme.Modules.pullback (f.fiberι y)).obj L)],
    ∃ V : Y.Opens, y ∈ V ∧ RelativelyAmple (f ∣_ V) (restrictToBasePreimage f L V))

end AlgebraicGeometry.RelativelyAmple
