module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Relative.Descent
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u v

/- Lemma 35.25.6: an invertible module is relatively ample if and only if all of its
canonical base changes along a given fpqc covering family are relatively ample. -/
@[stacks 0D2P] #check
  (AlgebraicGeometry.RelativelyAmple.iff_forall_baseChange_of_fpqcCovering :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules) [L.Invertible]
      {ι : Type v} (family : ι → Over S), Scheme.FpqcCovering family →
        (RelativelyAmple f L ↔
          ∀ i : ι, RelativelyAmple (pullback.snd f (family i).hom)
            (Scheme.Modules.baseChangeModule f (family i).hom L)))
