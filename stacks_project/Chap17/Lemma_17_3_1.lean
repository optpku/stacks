module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Stalk
public import ReasLib.Topology.Sheaves.Abelian.Sheafification
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

variable {X : RingedSpace.{u}}

/- Lemma 17.3.1 (1): the category of sheaves of modules on `X` is abelian. -/
@[stacks 01AG "(1)"]
#check (inferInstance : Abelian X.Modules)

/- Lemma 17.3.1 (2): exactness of a short complex of module sheaves is detected on stalks. -/
@[stacks 01AG "(2)"]
#check (RingedSpace.exact_iff_moduleStalkShortComplex_exact :
  ∀ S : ShortComplex X.Modules,
    S.Exact ↔ ∀ x : X, (RingedSpace.moduleStalkShortComplex S x).Exact)
