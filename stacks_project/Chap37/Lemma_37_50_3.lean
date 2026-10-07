module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Relative.Proper
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.RelativelyAmple

/- Lemma 37.50.3: an invertible module that is ample on the fibre of a proper morphism at a
point is relatively ample over some open neighbourhood of that point. -/
@[stacks 0D2S] #check
  (AlgebraicGeometry.RelativelyAmple.exists_morphismRestrict_of_isAmple_fiber :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
      (L : X.Modules) [L.Invertible] (y : Y)
      [Scheme.Modules.IsAmple ((Scheme.Modules.pullback (f.fiberι y)).obj L)],
      ∃ V : Y.Opens, y ∈ V ∧ RelativelyAmple (f ∣_ V) (restrictToBasePreimage f L V))

end AlgebraicGeometry.RelativelyAmple
