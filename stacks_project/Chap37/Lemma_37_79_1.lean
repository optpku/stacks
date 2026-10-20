module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Family.Relative
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u v

/- Lemma 37.79.1: an ample family on the target of a scheme morphism, together with the
existence of a relatively ample invertible module, yields an ample family on the source. -/
@[stacks 0GTP] #check
  (AlgebraicGeometry.Scheme.Modules.AmpleFamily.exists_of_relativelyAmple :
    ∀ {X Y : Scheme.{u}} {ι : Type v}
      (f : X ⟶ Y) (M : ι → Y.Modules)
      (hM : AlgebraicGeometry.Scheme.Modules.AmpleFamily M)
      (hL : ∃ L : X.Modules, RelativelyAmple f L),
      ∃ (κ : Type (max u v)) (N : κ → X.Modules),
        AlgebraicGeometry.Scheme.Modules.AmpleFamily N)
