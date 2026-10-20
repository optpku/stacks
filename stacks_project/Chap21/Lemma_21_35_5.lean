module

public import ReasLib.CategoryTheory.Monoidal.Closed.Source
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.35.5

The tensor-to-iterated-internal-Hom comparison is already owned by the generic source-order
closed-monoidal API.  The derived category of a ringed site is only a specialization, so this
chapter item keeps no second source-facing definition or proof-specific bridge.
-/

/- Lemma 21.35.5 (0A97): the canonical source-order map from
`RHom(L, M) ⊗ K` to `RHom(RHom(K, L), M)`. -/
@[stacks 0A97 "source-order tensor-to-iterated internal-Hom comparison"] #check
  @CategoryTheory.MonoidalClosed.Source.Iterated.map

/- The tensor-side specification and uncurried evaluation form are reusable companions. -/
@[stacks 0A97 "source-order tensor-to-iterated internal-Hom specification"] #check
  @CategoryTheory.MonoidalClosed.Source.Iterated.map_spec

@[stacks 0A97 "source-order tensor-to-iterated internal-Hom evaluation"] #check
  @CategoryTheory.MonoidalClosed.Source.Iterated.map_uncurry
