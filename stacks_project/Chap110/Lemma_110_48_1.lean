module

public import ReasLib.AlgebraicGeometry.GroupScheme.Counterexamples
import StacksCheckRecall

@[expose] public section

universe u

open AlgebraicGeometry
open scoped AlgebraicGeometry

/- Lemma 110.48.1: there exists a group scheme over the affine line which is
flat and of finite type, but not separated. -/
@[stacks 06E8] #check
  (AlgebraicGeometry.GroupScheme.exists_flat_finiteType_not_isSeparated_over_affineLine :
    ∀ {k : Type u} [Field k],
      ∃ G : AlgebraicGeometry.GroupScheme
          (𝔸(ULift.{u} (Fin 1); Spec (CommRingCat.of k))),
        AlgebraicGeometry.Flat G.X.hom ∧
          AlgebraicGeometry.Scheme.Hom.FiniteType G.X.hom ∧
            ¬ AlgebraicGeometry.IsSeparated G.X.hom)
