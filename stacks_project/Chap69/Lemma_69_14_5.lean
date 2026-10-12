/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap69.Lemma_69_14_5_Devissage
import StacksCheckRecall

open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open scoped ZeroObject

universe u

/- Lemma 69.14.5: let `S` be a scheme and let `X` be a Noetherian algebraic space
over `S`. Let `P` be an extension-closed property of coherent `𝒪_X`-modules which
contains the zero sheaf and descends from nonempty finite self-coproducts. If every
reduced closed subspace `i : Z ⟶ X` with `|Z|` irreducible admits a coherent sheaf
`G` on `Z` of full support such that every nonzero quasi-coherent ideal `I ⊂ 𝒪_Z`
contains a quasi-coherent `G' ⊂ I G` with support of `G / G'` proper closed in `|Z|`
and with `P` holding for `(pushforward i).obj G'`, then `P` holds for every coherent
sheaf on `X`. -/
@[stacks 07UT] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.devissagePropertyHoldsOfReducedClosedModels :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian X]
      (P : X.Modules → Prop),
      DevissageShortExactClosed P →
        DevissageDescendsFromFiniteCoproducts P →
          (∀ (Z : AlgebraicSpace S) (i : Z ⟶ X),
            IsClosedImmersion i → IsReduced Z → IsIrreducible Z →
              DevissageReducedClosedModel i P) →
            P (0 : X.Modules) →
              ∀ (F : X.Modules) [F.IsCoherent], P F)
