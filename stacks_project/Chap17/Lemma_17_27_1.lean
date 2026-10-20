module

public import ReasLib.Topology.Presheaf.Localization
import StacksCheckRecall

/-!
# Lemma 17.27.1

Localization of a commutative-ring presheaf has the expected universal properties and commutes
with stalks, both before and after sheafification.  The reusable owners live in ReasLib; this file
is the source-facing five-clause facade.
-/

@[expose] public section

/- Lemma 17.27.1 (01D0) (1): the canonical presheaf morphism to the objectwise
localization sends every distinguished section to a unit. -/
@[stacks 01D0 "(1), distinguished sections become units"]
#check @CategoryTheory.Presheaf.SubmonoidPresheaf.toLocalizationPresheaf_mapsToUnits

/- Lemma 17.27.1 (01D0) (2): a presheaf morphism which sends the distinguished
sections to units factors uniquely through the objectwise localization. -/
@[stacks 01D0 "(2), presheaf universal property"]
#check @CategoryTheory.Presheaf.SubmonoidPresheaf.Universal.existsUnique_lift

/- Lemma 17.27.1 (01D0) (3): at every point, the stalk of the objectwise
localization is the localization of the original stalk at the submonoid of distinguished germs. -/
@[stacks 01D0 "(3), localization commutes with stalks"]
#check @TopCat.Presheaf.SectionLocalization.stalkIsLocalization

/- Lemma 17.27.1 (01D0) (4): after sheafification, a morphism which inverts the
distinguished sections factors uniquely through the sheafified localization. -/
@[stacks 01D0 "(4), sheafified universal property"]
#check @CategoryTheory.Presheaf.SubmonoidPresheaf.Sheafification.existsUnique_lift

/- Lemma 17.27.1 (01D0) (5): the stalk of the sheafified localization is still the
localization of the original stalk at the submonoid of distinguished germs. -/
@[stacks 01D0 "(5), sheafification preserves localized stalks"]
#check @TopCat.Presheaf.SectionLocalization.sheafifiedStalkIsLocalization
