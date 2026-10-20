/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Sections
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

/- Lemma 26.21.11 (1): every section of a scheme morphism is an immersion. -/
@[stacks 01KT] #check Scheme.Hom.Section.isImmersion

/- Lemma 26.21.11 (2): a section of a separated morphism is a closed immersion. -/
@[stacks 01KT] #check Scheme.Hom.Section.isClosedImmersion

/- Lemma 26.21.11 (3): a section of a quasi-separated morphism is quasi-compact. -/
@[stacks 01KT] #check Scheme.Hom.Section.quasiCompact
