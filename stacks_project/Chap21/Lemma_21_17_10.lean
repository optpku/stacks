module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.UpperResolution.Generators
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.17.10

The localized-generator object property and its upper-truncation resolution are canonical ReasLib
owners.  This chapter file is a recall surface only; it does not duplicate coproduct flattening,
epi-cover, or sequential-colimit arguments.
-/

open CategoryTheory
open CategoryTheory.ObjectProperty
open SheafOfModules.RingedSite

/- Lemma 21.17.10 (077J): the canonical object property of coproducts of localized structure
modules, together with its reusable closure and cover infrastructure. -/
@[stacks 077J "localized-generator coproduct property"] #check
  @localizedGeneratorCoproducts

@[stacks 077J "localized-generator coproducts contain zero"] #check
  @localizedGeneratorCoproducts_containsZero

@[stacks 077J "localized-generator coproducts are finitely coproduct closed"] #check
  @localizedGeneratorCoproducts_isClosedUnderFiniteCoproducts

@[stacks 077J "localized-generator coproducts give epi covers"] #check
  @localizedGeneratorCoproducts_hasEpiCover

/- Lemma 21.17.10 (077J): every module complex has an upper-truncation resolution by the
localized-generator property whose colimit comparison is a quasi-isomorphism. -/
@[stacks 077J "upper resolution by localized generators"] #check
  @exists_upperResolution_of_localizedGenerators
