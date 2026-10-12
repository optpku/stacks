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
# Lemma 21.34.2

The internal-Hom composition morphism is owned by the generic source-order closed-monoidal API.
No ringed-site alias is needed for the chapter specialization.
-/

/- Lemma 21.34.2 (0A91): source-order internal-Hom composition. -/
@[stacks 0A91 "source-order internal-Hom composition"] #check
  @CategoryTheory.MonoidalClosed.Source.comp

@[stacks 0A91 "internal-Hom composition specification"] #check
  @CategoryTheory.MonoidalClosed.Source.comp_spec

@[stacks 0A91 "internal-Hom composition naturality"] #check
  @CategoryTheory.MonoidalClosed.Source.comp_natural_target
@[stacks 0A91 "internal-Hom composition source naturality"] #check
  @CategoryTheory.MonoidalClosed.Source.comp_natural_source
@[stacks 0A91 "internal-Hom composition middle naturality"] #check
  @CategoryTheory.MonoidalClosed.Source.comp_natural_middle
