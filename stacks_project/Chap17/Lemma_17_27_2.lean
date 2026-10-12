/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.SectionLocalization
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SectionLocalization
import StacksCheckRecall

/-!
# Lemma 17.27.2

Localization of modules is scalar extension along the localized coefficient ring.  The
presheaf owner exposes both the change-of-rings universal property and its sectionwise
`IsLocalizedModule` specification; the sheaf owner gives the corresponding intrinsic
extension-of-scalars model after sheafification.
-/

@[expose] public section

/- Lemma 17.27.2 (01D1) (1): the localized module presheaf is extension of scalars
along `O ⟶ S⁻¹O`. -/
@[stacks 01D1 "(1), localized module presheaf"]
#check @PresheafOfModules.SectionLocalization.functor

/- The preceding owner is sectionwise the usual localization
`F(U) ⟶ S(U)⁻¹F(U)`, rather than merely an unspecified left adjoint. -/
#check @PresheafOfModules.SectionLocalization.unit_isSectionwiseLocalization

/- Its maps are governed by the reusable extension/restriction universal property. -/
#check @PresheafOfModules.SectionLocalization.existsUnique_lift
#check @PresheafOfModules.SectionLocalization.hom_ext

/- Lemma 17.27.2 (01D1) (2): for module sheaves, localization is canonically
extension of scalars along the sheafified localization map, i.e. the intrinsic form of
`S⁻¹O ⊗_O F`. -/
@[stacks 01D1 "(2), sheafified localization as scalar extension"]
#check @SheafOfModules.RingedSite.SectionLocalization.extensionIso
#check @SheafOfModules.RingedSite.SectionLocalization.hom_ext

/- The comparison is available in both directions as named pointwise morphisms. -/
#check @SheafOfModules.RingedSite.SectionLocalization.extensionHom
#check @SheafOfModules.RingedSite.SectionLocalization.extensionInv
#check @SheafOfModules.RingedSite.SectionLocalization.extensionIso_hom_app
#check @SheafOfModules.RingedSite.SectionLocalization.extensionIso_inv_app

/- Both comparison maps are natural in the module sheaf. -/
#check @SheafOfModules.RingedSite.SectionLocalization.extensionHom_naturality
#check @SheafOfModules.RingedSite.SectionLocalization.extensionInv_naturality

/- The pointwise comparison identifies the localization unit with the canonical
extension-restriction unit in both directions. -/
#check @SheafOfModules.RingedSite.SectionLocalization.unit_extensionHom
#check @SheafOfModules.RingedSite.SectionLocalization.extendUnit_extensionInv
