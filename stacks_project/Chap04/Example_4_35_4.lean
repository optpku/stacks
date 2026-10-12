/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.SingleObj.Fiberedness
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor Functor.Fiber
open CategoryTheory.SingleObj

universe u v

namespace MonoidHom

variable {G : Type u} {H : Type v} [Group G] [Group H]
variable (p : G →* H)

/- The categorical fiber over the unique object contains only vertical arrows. For a one-object
functor induced by `p`, verticality is exactly membership in `p.ker`. Mathlib 4.32 has canonical
owners for `MonoidHom.toFunctor`, `Functor.Fiber`, and `Functor.asEquivalence`, but no existing
bridge identifying this fiber with `SingleObj p.ker`; the explicit functor below is therefore the
smallest reusable new data owner. -/

/- Example 4.35.4 (2): the standard fiber of `p.toFunctor` over the unique base object is
equivalent to the one-object groupoid associated to `p.ker`.

The non-Prop data is obtained from the explicit `MonoidHom.KernelFiber.toFiber`; only its equivalence laws
are deferred in `MonoidHom.KernelFiber.toFiber.isEquivalence`. This keeps downstream computations tied to
the concrete kernel inclusion rather than to a whole-declaration choice placeholder. -/
@[stacks 003U "(2)"]
#check (MonoidHom.KernelFiber.equivalence p :
  p.toFunctor.Fiber (star H) ≌ SingleObj p.ker)

/- Example 4.35.4 (1): the one-object functor induced by a group homomorphism `p : G →* H` is
fibred in groupoids if and only if `p` is surjective.

Proof strategy: apply
`CategoryTheory.Functor.IsFibered.InGroupoids.iff_isFibered_fibersGroupoid`. The fibredness component is
`MonoidHom.toFunctor.isFibered_iff_surjective`; the unique standard fiber is a groupoid because
`MonoidHom.KernelFiber.equivalence p` identifies it with `SingleObj p.ker`. In the reverse implication,
forget the fibred-in-groupoids structure to its canonical `Functor.IsFibered` field. -/
@[stacks 003U "(1)"]
#check (MonoidHom.toFunctor.inGroupoids_iff_surjective p :
  CategoryTheory.Functor.IsFibered.InGroupoids p.toFunctor ↔
    Function.Surjective p)

end MonoidHom
