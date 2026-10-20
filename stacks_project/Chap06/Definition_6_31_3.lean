module

public import ReasLib.Topology.Sheaf.ExtensionByInitial
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopCat TopologicalSpace

noncomputable section

universe v

/-
Domain-style sampling for Definition 6.31.3:
- primary domain: extension by zero / by the initial object along the inclusion `j : U ↪ X` of an
  open subset, specialized to set-valued presheaves and sheaves;
- sampled owner declarations:
  `TopCat.Opens.Subspace.space`,
  `TopCat.Presheaf.ExtensionByInitial.functor`,
  `TopCat.Sheaf.ExtensionByInitial.functor`;
- owner abstraction: the canonical owners are the presheaf and sheaf functors above on the open
  subspace `TopCat.Opens.Subspace.space U`; this file should specialize those owners to
  `Type v` rather than introduce a parallel set-specific wrapper;
- primitive data versus derived API: the primitive input is the open subset `U`, together with the
  canonical open-subspace object and the upstream extension-by-initial-object owners. The
  set-valued “extension by the empty set” phrasing is derived from the fact that the initial object
  of `Type v` is the empty type, and the sheaf-level construction is derived by sheafifying the
  presheaf-level owner.

Source/core/bridge triage:
- `source-facing`: the Stacks set-valued phrasing “extension by the empty set” on an open subset;
- `core/canonical`: `TopCat.Presheaf.ExtensionByInitial.functor` and
  `TopCat.Sheaf.ExtensionByInitial.functor`;
- `bridge/view`: the specialization `C = Type v`, where the initial object is the empty type.
-/

section

variable {X : TopCat.{v}}

section PresheafCase

variable (U : Opens X)

/- The canonical owner construction for extension by the initial object along an open subset is
`TopCat.Presheaf.ExtensionByInitial.functor`. -/
recall TopCat.Presheaf.ExtensionByInitial.functor

/- Definition 6.31.3 (1): for presheaves of sets on an open subset
`U ⊆ X`, extension by the empty set is the `Type v` specialization `jₚ! U`; in `Type v`, the
initial object is the empty type. -/
@[stacks 00A2 "presheaf extension by the empty set"]
#check
  (jₚ! U :
    (TopCat.Opens.Subspace.space U).Presheaf (Type v) ⥤ X.Presheaf (Type v))

end PresheafCase

section SheafCase

variable (U : Opens X)

/- The canonical owner construction for sheaf-level extension by the initial object along an open
subset is `TopCat.Sheaf.ExtensionByInitial.functor`. -/
recall TopCat.Sheaf.ExtensionByInitial.functor

/- Definition 6.31.3 (2): for sheaves of sets on an open subset
`U ⊆ X`, extension by the empty set is the `Type v` specialization `j! U`; by definition it is
obtained by sheafifying the presheaf-level construction. -/
@[stacks 00A2 "sheafification of presheaf extension by the empty set"]
#check
  (j! U :
    (TopCat.Opens.Subspace.space U).Sheaf (Type v) ⥤ X.Sheaf (Type v))

end SheafCase

end
