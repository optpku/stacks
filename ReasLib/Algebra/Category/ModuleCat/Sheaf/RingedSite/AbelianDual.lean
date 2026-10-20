module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.AbelianDual.Functor
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.AbelianDual.Evaluation
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.AbelianDual.Exact
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.AbelianDual.Resolution
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.AbelianDual.InjectiveTarget.Existence

/-!
# Abelian-sheaf-valued duals of module sheaves

This is the aggregate entry point for abelian duals on a ringed site:

* `AbelianDual.Functor` constructs local Homs, their precomposition action, the resulting module
  sheaf, and the contravariant additive dual functor;
* `AbelianDual.Evaluation` constructs canonical bidual evaluation and its monomorphism criterion;
* `AbelianDual.Exact` provides exactness and the generic injective flat-bidual API;
* `AbelianDual.Resolution` combines the canonical free flat cover with an injective coseparator
  to construct functorial injective embeddings.

Downstream files needing only one layer should import that leaf directly.
-/

@[expose] public section

open CategoryTheory

namespace SheafOfModules.RingedSite.AbelianDual

end SheafOfModules.RingedSite.AbelianDual
