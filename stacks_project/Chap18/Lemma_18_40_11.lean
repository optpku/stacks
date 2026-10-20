/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.LocalHom
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- Lemma 18.40.11 (04KR) (1): the canonical inverse-image presentation has a cartesian units
square. -/
@[stacks 04KR "(1)"]
#check @RingedSite.Hom.ofPullback_unitsSquareCartesian

/- Lemma 18.40.11 (04KR) (2): the canonical inverse-image presentation is a local morphism. -/
@[stacks 04KR "(2)"]
#check @RingedSite.Hom.ofPullback_isLocal

/- The bundled inverse-image morphism is explicit reusable data, not an existential witness. -/
#check @RingedSite.Hom.ofPullback
