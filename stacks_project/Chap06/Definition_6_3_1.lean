module

public import ReasLib.Topology.Sheaf.Notation
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory

open scoped TopCat

variable (X : TopCat.{u})

/- Domain-style sampling for Definition 6.3.1:
- primary domain: set-valued presheaves on a topological space;
- verified owner API: `TopCat.Presheaf`, `TopCat.instCategoryPresheaf`, and
  `CategoryTheory.NatTrans.naturality`;
- best owner abstraction: the canonical presheaf owner `X.Presheaf (Type v)`, with the shared
  Stacks-style notation `PSh(X)`;
- primitive data: only the functor `(TopologicalSpace.Opens X)ᵒᵖ ⥤ Type v`;
- derived API: morphisms as natural transformations, hence compatibility with restriction maps by
  naturality.

Source/core/bridge triage:
- `source-facing`: the Stacks category `PSh(X)` of set-valued presheaves on `X`;
- `core/canonical`: `TopCat.Presheaf`;
- `bridge/view`: the naturality identities for morphisms of presheaves.

This item adds no extra source-facing mathematics beyond the canonical owner, so the main entry
should be a direct recall of `TopCat.Presheaf` together with the shared notation `PSh(X)`,
rather than a duplicate local wrapper. -/

/- Definition 6.3.1 (1): a presheaf of sets on `X` is the canonical functor
`(TopologicalSpace.Opens X)ᵒᵖ ⥤ Type v`, with restriction identity and composition supplied by the
functor laws. -/
@[stacks 006E "set-valued presheaves on a topological space"]
recall TopCat.Presheaf

/- Definition 6.3.1 (2): presheaves form a category whose morphisms are natural transformations. -/
@[stacks 006E "category structure and morphisms of set-valued presheaves"]
#check TopCat.instCategoryPresheaf

/- Definition 6.3.1 (3): the category of presheaves of sets on `X` is denoted `PSh(X)`. -/
@[stacks 006E "the category PSh(X) of set-valued presheaves"]
#check (PSh(X))
#check (X.Presheaf (Type v))

section

variable {X}
variable {F G : PSh(X)} (φ : F ⟶ G)

/- Definition 6.3.1 (4): compatibility of a presheaf morphism with restriction maps is the
naturality identity. -/
@[stacks 006E "compatibility of presheaf morphisms with restriction maps"]
#check φ.naturality

end
