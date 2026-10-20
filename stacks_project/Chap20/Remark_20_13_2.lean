module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Acyclic
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pushforward.Acyclic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Sections.Pushforward
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

/-!
# Computing derived sections after direct image

This remark explains the derived comparison from Lemma 20.13.1 using an injective resolution.
The reusable API records the derived isomorphism directly; the underived sections identity and
the two acyclicity facts are its independent ingredients.
-/

/- Remark 20.13.2: an injective resolution computes derived sections on the source, its direct
image computes derived direct image and then derived sections on the target, and the resulting
derived sections are canonically identified. -/
@[stacks 01F0]
#check fun {X Y : RingedSpace.{u}} (f : X ⟶ Y) =>
  RingedSpace.Module.Derived.Sections.Pushforward.iso f (⊤ : Opens Y.carrier)

/- Direct image of an injective is acyclic for sections, which is the non-formal input in the
injective-resolution computation. -/
#check @RingedSite.Hom.modulePushforward.isTotallyAcyclic_of_injective
#check @RingedSite.Hom.ModuleSections.rightAcyclicForGlobalSections

/- The final termwise identification is the underived top-open component of the natural
sections/direct-image isomorphism. -/
#check @AlgebraicGeometry.RingedSpace.Module.Sections.Pushforward.globalSectionIso
#check @AlgebraicGeometry.RingedSpace.Module.Sections.Pushforward.globalIso

/- The bounded-below composition comparison is the ringed-space specialization used by the
commutative derived diagram. -/
#check @AlgebraicGeometry.RingedSpace.Module.Derived.Sections.Pushforward.sourceComparisonIso
#check @AlgebraicGeometry.RingedSpace.Module.Derived.Sections.Pushforward.targetComparisonIso
#check @RingedSite.Hom.ModuleSections.objectPushforwardIso
