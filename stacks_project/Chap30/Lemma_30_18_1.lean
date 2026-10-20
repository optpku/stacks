module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Chow
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 30.18.1: a separated finite-type morphism `f : X ⟶ S` to a Noetherian scheme admits a
proper surjective morphism `π : X' ⟶ X` and an immersion of `X'` into some relative projective
space over `S`, compatible with `f`; moreover, `π` is an isomorphism over a dense open of `X`.
-/
@[stacks 0200]
#check (AlgebraicGeometry.ChowLemmaModification.exists_of_separated_finiteType :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S] [IsSeparated f]
    [Scheme.Hom.FiniteType f], Nonempty (ChowLemmaModification f))
