module

public import ReasLib.Algebra.Homology.CochainComplex.InjectiveResolution
public import ReasLib.Algebra.Homology.HomotopyCategory.Termwise
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Bounded-Below Injective Homotopy Categories

This leaf specializes the property-neutral bounded-below termwise homotopy
infrastructure from `HomotopyCategory.Termwise` to injective resolutions. It
separates the intrinsic full subcategory of termwise-injective complexes from
a noncanonical choice of resolutions and from derived-category localization
results.

## Main declarations

* `HomotopyCategory.Plus.injective` and `HomotopyCategory.Plus.Injective` are
  the injective specialization of the generic termwise category.
* `CochainComplex.InjectivePlus.toHomotopy` is its cochain-to-homotopy bridge.

The noncanonical choice and functorial realization of injective resolutions
are owned by `Injective/Resolution.lean`.

The notation `K⁺ᵢ(A)` is scoped in `CategoryTheory` and keeps the ambient
category explicit.
-/

open CategoryTheory
open CategoryTheory.ObjectProperty

universe v u

namespace CategoryTheory

namespace HomotopyCategory.Plus

variable (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜]

/-- Stacks 013W: the termwise-injective specialization of `termsIn`. -/
@[stacks 013W]
abbrev injective : ObjectProperty (HomotopyCategory.Plus 𝒜) :=
  termsIn 𝒜 (isInjective 𝒜)

/-- Stacks 013W: the bounded-below homotopy category of complexes with
injective terms. -/
@[stacks 013W]
abbrev Injective :=
  TermsIn 𝒜 (isInjective 𝒜)

/-- Bounded-below homotopy objects with injective terms form a triangulated
full subcategory. -/
@[stacks 014W]
instance : (injective 𝒜).IsTriangulated := sorry

namespace Injective

/-- The canonical inclusion of bounded-below injective homotopy objects into
the bounded-below homotopy category. -/
abbrev ι : Injective 𝒜 ⥤ HomotopyCategory.Plus 𝒜 :=
  TermsIn.ι 𝒜

/-- The canonical inclusion of bounded-below injective homotopy objects is
fully faithful. -/
abbrev fullyFaithfulι : (ι 𝒜).FullyFaithful :=
  TermsIn.fullyFaithfulι 𝒜

/-- The underlying cochain complex of a bounded-below injective homotopy
object is bounded below. -/
theorem plus (I : Injective 𝒜) :
    CochainComplex.plus 𝒜 I.obj.obj.as := sorry

/-- Every term of the underlying cochain complex of a bounded-below injective
homotopy object is injective. -/
theorem term_injective (I : Injective 𝒜) (n : ℤ) :
    _root_.CategoryTheory.Injective (I.obj.obj.as.X n) := sorry

/-- The underlying cochain complex of a bounded-below injective homotopy
object is K-injective. -/
theorem isKInjective (I : Injective 𝒜) :
    CochainComplex.IsKInjective I.obj.obj.as := sorry

/-- A bounded-below injective homotopy object, viewed as a bounded-below
cochain complex with injective terms. -/
@[stacks 013W]
noncomputable abbrev toInjectivePlus (I : Injective 𝒜) :
    CochainComplex.InjectivePlus 𝒜 :=
  TermsIn.toCochain 𝒜 I

end Injective

end HomotopyCategory.Plus

/-- The scoped notation for the bounded-below homotopy category of injective
objects. -/
scoped[CategoryTheory] notation:max "K⁺" "ᵢ(" A:arg ")" =>
  HomotopyCategory.Plus.Injective A

end CategoryTheory

namespace CochainComplex

variable (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜]

namespace InjectivePlus

/-- The termwise-injective specialization of the generic homotopy quotient
bridge. -/
@[stacks 013W]
noncomputable abbrev toHomotopy :
    InjectivePlus 𝒜 ⥤ HomotopyCategory.Plus.Injective 𝒜 :=
  CochainComplex.Plus.TermsIn.toHomotopy 𝒜 (isInjective 𝒜)

end InjectivePlus

end CochainComplex
