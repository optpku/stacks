module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Coherent.Devissage
import StacksCheckRecall

open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open scoped ZeroObject

universe u

/- Lemma 69.14.6: let `S` be a scheme and let `X` be a Noetherian algebraic space
over `S`. Let `P` be a property of coherent `𝒪_X`-modules satisfying two-out-of-three
on coherent short exact sequences and descending from nonempty finite self-coproducts.
If every reduced closed subspace `i : Z ⟶ X` with `|Z|` irreducible admits a coherent
sheaf `G` on `X` whose scheme-theoretic support is `i` such that `P` holds for `G`,
and if `P` holds for the zero sheaf, then `P` holds for every coherent sheaf on `X`. -/
@[stacks 08AN] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.devissagePropertyHoldsOfSchemeTheoreticSupportModels :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian X]
      (P : X.Modules → Prop),
      DevissageTwoOutOfThree P →
        DevissageDescendsFromFiniteCoproducts P →
          (∀ (Z : AlgebraicSpace S) (i : Z ⟶ X),
            IsClosedImmersion i → IsReduced Z → IsIrreducible Z →
              DevissageSchemeTheoreticSupportModel i P) →
            P (0 : X.Modules) →
              ∀ (F : X.Modules) [F.IsCoherent], P F)
