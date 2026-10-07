module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Etale
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v

/- Lemma 38.2.4: Let `f : T ⟶ S` be an étale morphism, let `t : T`, and let `M` be a
module over `T.presheaf.stalk t`. Then `M` is flat after restriction along `f.stalkMap t` if and
only if it is flat over `T.presheaf.stalk t`. -/
@[stacks 05BA] #check (AlgebraicGeometry.Etale.flatAlong_stalkMap_iff :
  ∀ {T S : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ S) [AlgebraicGeometry.Etale f]
    (t : T) (M : Type v) [AddCommGroup M] [Module (T.presheaf.stalk t) M],
    Module.FlatAlong (f.stalkMap t).hom M ↔ Module.Flat (T.presheaf.stalk t) M)
