module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Derived.SectionsComparison
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpensRingedSite
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Sections.Pushforward
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open TopologicalSpace
open scoped RingedSpace.Hom

noncomputable section

universe u z

namespace AlgebraicGeometry.RingedSpace

/-!
Lemma 20.13.1 is the ringed-space specialization of the objectwise sections/direct-image
comparison on the opens ringed site.  The reusable owner is the generic
`RingedSite.Hom.ModuleSections` API: it keeps the section-ring restriction explicit and exposes
both the derived comparison and its isomorphism, without introducing a bounded-derived local
model or a chapter-specific `rightDerivedCompComparison` alias.
-/

/- Lemma 20.13.1: for `f : X ⟶ Y` and `V ⊆ Y`, sections over `f ⁻¹ᵁ V` followed by restriction
of scalars agree, after deriving, with sections over `V` after direct image. -/
@[stacks 01EZ]
#check @RingedSite.Hom.ModuleSections.objectPushforwardComparison

@[stacks 01EZ]
#check @Module.Sections.Pushforward.functor_eq

@[stacks 01EZ]
#check @Module.Derived.Sections.Pushforward.iso

/- The comparison is invertible, and its natural-isomorphism form is the preferred downstream API. -/
@[stacks 01EZ]
#check @RingedSite.Hom.ModuleSections.objectPushforwardComparison_isIso

@[stacks 01EZ]
#check @RingedSite.Hom.ModuleSections.objectPushforwardIso

#check @Module.Derived.Sections.Pushforward.sourceComparisonIso
#check @Module.Derived.Sections.Pushforward.targetComparisonIso
#check @Module.Derived.Sections.Pushforward.appIso

/- The opens-site bridge is the canonical specialization from ringed spaces. -/
@[stacks 01EZ]
#check @opensRingedSiteHom

end AlgebraicGeometry.RingedSpace
