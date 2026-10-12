/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.Sieves
public import StacksCheckRecall.CommandCrossRef

@[expose] public section

namespace CategoryTheory

/- Domain-style sampling for 7.49.3.1:
- primary domain: iterated refinement of sieves on a category;
- sampled owner abstractions:
  `Presieve.bind`,
  `Presieve.BindStruct`,
  `Sieve.bind`,
  `Sieve.BindStruct`;
- source-facing layer: the sieve obtained by refining each arrow of a sieve by a further sieve on
  its domain;
- core/canonical owner: `Sieve.bind`, whose owner interface is slightly more general and takes an
  initial `Presieve`;
- bridge/view layer: `Sieve.BindStruct` together with the structural conversion
  `Presieve.BindStruct.bind`.

Primitive data are the source-facing sieve `S` on `X` and the sieve-valued refinement family `R`.
At the owner level mathlib packages the same construction for an arbitrary initial presieve, so the
source sieve case is handled by direct recall of that canonical owner. The factorization package
`BindStruct` and the structural map from factorization data to membership are derived API owned
upstream by mathlib, so this file recalls those owners directly. The noncomputable selector
`Presieve.bind.bindStruct` is intentionally not exposed here because it chooses one witness from an
existential statement and is not part of the canonical public surface.
-/

/- Theorem 7.49.3 (00ZJ), equation (7.49.3.1): the source-facing refinement of a sieve by
sieve-valued refinements is the canonical
owner `Sieve.bind`. Mathlib defines this owner slightly more generally for an initial presieve
`S`, and the sieve case of the source is the intended specialization. -/
@[stacks 00ZJ "equation (7.49.3.1)"] #check @Sieve.bind

/- Companion recall: a morphism `h : Z ⟶ X` in `Sieve.bind S R` is equivalently encoded by the
structured factorization datum `Sieve.BindStruct S R h`. This is the canonical factorization
interface for membership in a bound sieve. -/
#check @Sieve.BindStruct

/- Companion recall: a factorization datum in `BindStruct` canonically determines membership in the
corresponding bound presieve, hence also in the sieve `Sieve.bind S R` when `R` is sieve-valued. -/
#check @Presieve.BindStruct.bind

end CategoryTheory
