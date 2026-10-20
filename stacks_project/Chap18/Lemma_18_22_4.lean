/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Localization.Representable
import StacksCheckRecall

@[expose] public section

/- Lemma 18.22.4 (04J9): the arrow `c : U ⟶ f.base.obj V` supplies the precise
representable parameter of the slice-topos localized morphism. -/
#check @RingedSite.Localization.Representable.parameter

/- The identifications of Lemma 18.21.3 carry the restricted structure sheaf to the
slice-product structure object over the sheafified representable. -/
#check @RingedSite.Localization.Representable.structureObjectComparison_isIso

/- Under the representable-localization comparisons, the site-localized morphism is the
slice-topos morphism localized at that parameter. -/
#check @RingedSite.Localization.Representable.localizedInverseImage

/- Lemma 18.22.4 (04J9) (1): the ambient square of Lemma 18.20.2 is the representable
specialization of the ambient square of Lemma 18.22.3. -/
@[stacks 04J9 "ambient square"]
#check @RingedSite.Localization.Representable.ambientSquare

/- The slice-topos ambient square carries explicit comparison data, independently of the
Prop-valued site-presentation comparison. -/
#check @RingedSite.Localization.Representable.ambientIso

/- Its comparison respects the localized underlying structure map. -/
#check @RingedSite.Localization.Representable.ambientIso_structure

/- A commuting square `(c', b, a, c)` induces the corresponding square of representable
localization parameters. -/
#check @RingedSite.Localization.Representable.parameter_naturality

/- Lemma 18.22.4 (04J9) (2): the relocalization square of Lemma 18.20.2 is the representable
specialization of the base-change square of Lemma 18.22.3. -/
@[stacks 04J9 "relocalization square"]
#check @RingedSite.Localization.Representable.relocalizationSquare

/- The same base-change comparison is compatible with the two localized structure maps. -/
#check @RingedSite.Localization.Representable.structureMap_commSq
