/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Monoidal.Closed.Source
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.35.6

The source-order composition morphism in the derived category is the generic braided
closed-monoidal `Source.comp`.  Its defining formula and variance API are reusable for every
closed monoidal model, so the chapter item is a direct recall.
-/

/- Lemma 21.35.6 (0A98): the canonical composition morphism
`RHom(L, M) ⊗ RHom(K, L) ⟶ RHom(K, M)`. -/
@[stacks 0A98 "source-order internal-Hom composition"] #check
  @CategoryTheory.MonoidalClosed.Source.comp

@[stacks 0A98 "source-order internal-Hom composition specification"] #check
  @CategoryTheory.MonoidalClosed.Source.comp_spec

@[stacks 0A98 "source-order internal-Hom composition target naturality"] #check
  @CategoryTheory.MonoidalClosed.Source.comp_natural_target

@[stacks 0A98 "source-order internal-Hom composition source naturality"] #check
  @CategoryTheory.MonoidalClosed.Source.comp_natural_source

@[stacks 0A98 "source-order internal-Hom composition middle naturality"] #check
  @CategoryTheory.MonoidalClosed.Source.comp_natural_middle
