module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.WeaklyAssociatedPoints.Zero
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

universe u

/- Lemma 71.2.5: a quasi-coherent module on an algebraic space over a scheme
is zero if and only if its weakly associated locus is empty. -/
@[stacks 0CU0] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.isZero_iff_weakAss_eq_empty :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules) [F.IsQuasicoherent],
      IsZero F ↔ F.weakAss = (∅ : Set (Points X)))
