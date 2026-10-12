/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Functor.Derived.ComputesAt
public import ReasLib.CategoryTheory.Functor.Derived.DefinedAt.Stability
public import ReasLib.CategoryTheory.Functor.FullyFaithful.Source
public import ReasLib.CategoryTheory.Functor.FullyFaithful.Target
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Computing Derived Values from Endpoint Full Faithfulness

For a localization functor, full faithfulness on the hom-sets ending at one object makes the
identity right denominator terminal.  The sourcewise dual makes the identity left denominator
initial.  These endpoint conditions are exactly what injective and projective objects provide;
global full faithfulness of the localization is unnecessary.
-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']

namespace RightDerived.IdentityDenominator

variable {F : D ⥤ D'} {S : MorphismProperty D} {X : D}

/-- Targetwise full faithfulness of the localization makes the right-derived indexing diagram
essentially constant. -/
@[stacks 05S9 "terminal identity denominator"]
theorem isEssentiallyConstant (hQ : S.Q.FullyFaithfulTo X) :
    IsFiltered.IsEssentiallyConstant
      (CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F) := sorry

/-- Targetwise full faithfulness of the localization makes the right-derived value source-defined
at the chosen object. -/
@[stacks 05S9 "terminal identity denominator"]
theorem definedAt (hQ : S.Q.FullyFaithfulTo X) :
    RightDerived.DefinedAt F S X := sorry

/-- A terminal identity denominator supplies Mathlib's pointwise right-derived existence
predicate. -/
@[stacks 05S9 "terminal identity denominator"]
theorem hasPointwise (hQ : S.Q.FullyFaithfulTo X) :
    F.HasPointwiseRightDerivedFunctorAt S X := sorry

/-- The identity-denominator leg into a pointwise right-derived value is an isomorphism under
targetwise full faithfulness. -/
@[stacks 05SX "terminal identity denominator"]
theorem isIso_valueLeg [S.ContainsIdentities] (hQ : S.Q.FullyFaithfulTo X)
    [F.HasPointwiseRightDerivedFunctorAt S X] :
    IsIso (CategoryTheory.Functor.RightDerived.Value.ι F S (𝟙 X) (S.id_mem X)) := sorry

/-- A terminal identity denominator makes the chosen object compute every pointwise
right-derived value. -/
@[stacks 05SX "terminal identity denominator"]
theorem computesAt [S.ContainsIdentities] (hQ : S.Q.FullyFaithfulTo X) :
    RightDerived.ComputesAt F S X := sorry

end RightDerived.IdentityDenominator

namespace LeftDerived.IdentityDenominator

variable {F : D ⥤ D'} {S : MorphismProperty D} {X : D}

/-- Sourcewise full faithfulness of the localization makes the left-derived indexing diagram
essentially constant. -/
@[stacks 05S9 "initial identity denominator"]
theorem isEssentiallyConstant (hQ : S.Q.FullyFaithfulFrom X) :
    IsCofiltered.IsEssentiallyConstant
      (StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F) := sorry

/-- Sourcewise full faithfulness of the localization makes the left-derived value source-defined
at the chosen object. -/
@[stacks 05S9 "initial identity denominator"]
theorem definedAt (hQ : S.Q.FullyFaithfulFrom X) :
    LeftDerived.DefinedAt F S X := sorry

/-- An initial identity denominator supplies Mathlib's pointwise left-derived existence
predicate. -/
@[stacks 05S9 "initial identity denominator"]
theorem hasPointwise (hQ : S.Q.FullyFaithfulFrom X) :
    F.HasPointwiseLeftDerivedFunctorAt S X := sorry

/-- The identity-denominator projection from a pointwise left-derived value is an isomorphism
under sourcewise full faithfulness. -/
@[stacks 05SX "initial identity denominator"]
theorem isIso_valueProjection [S.ContainsIdentities] (hQ : S.Q.FullyFaithfulFrom X)
    [F.HasPointwiseLeftDerivedFunctorAt S X] :
    IsIso (CategoryTheory.Functor.LeftDerived.Value.π F S (𝟙 X) (S.id_mem X)) := sorry

/-- An initial identity denominator makes the chosen object compute every pointwise left-derived
value. -/
@[stacks 05SX "initial identity denominator"]
theorem computesAt [S.ContainsIdentities] (hQ : S.Q.FullyFaithfulFrom X) :
    LeftDerived.ComputesAt F S X := sorry

end LeftDerived.IdentityDenominator


end CategoryTheory.Functor
