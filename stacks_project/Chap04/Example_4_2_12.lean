/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.SingleObj.MapProperties
import StacksCheckRecall

@[expose] public section


open CategoryTheory

universe u

namespace MonoidHom

variable {G H : Type u} [Group G] [Group H]
variable (p : G →* H)

/- `SingleObj.mapHom`, exposed by `MonoidHom.toFunctor`, is the canonical construction of the
induced functor. The source is uniformly stated for groups; the two companion theorems specialize
faithfulness and full faithfulness to that same group-level input. -/

/- Example 4.2.12 (1): a group homomorphism `p : G →* H` induces the canonical functor
`p.toFunctor : SingleObj G ⥤ SingleObj H`. -/
@[stacks 001F "group homomorphism as a functor between one-object groupoids"]
#check (p.toFunctor : SingleObj G ⥤ SingleObj H)

/- Example 4.2.12 (2): the induced functor `p.toFunctor` is faithful exactly when the group
homomorphism `p` is injective. -/
@[stacks 001F "faithfulness of the induced one-object functor"]
#check (toFunctor.faithful_iff_injective p :
  p.toFunctor.Faithful ↔ Function.Injective p)

/- The same neutral API also identifies fullness and equivalence. -/
#check toFunctor.full_iff_surjective p
#check toFunctor.isEquivalence_iff_bijective p

/- `Functor.FullyFaithful.nonempty_iff_map_bijective` reduces full faithfulness to hom-set
bijectivity, and `ConcreteCategory.isIso_iff_bijective` recognizes bijective group morphisms as
isomorphisms. Neither theorem alone is the source comparison, so the bridge uses the canonical
predicates directly, preserves the group-level scope, and exposes an `IsIso` fact for reuse. -/

/- Example 4.2.12 (3): the induced functor `p.toFunctor` is fully faithful exactly when the
corresponding morphism `GrpCat.ofHom p` is an isomorphism in `GrpCat`. -/
@[stacks 001F "full faithfulness of the induced one-object functor"]
#check (toFunctor.fullyFaithful_iff_isIso p :
  Nonempty p.toFunctor.FullyFaithful ↔ IsIso (GrpCat.ofHom p))

/- The monoid-level core avoids passing through `GrpCat` when only hom-set bijectivity is needed. -/
#check toFunctor.fullyFaithful_iff_bijective p

end MonoidHom
