/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.Tactic.CrossRefAttribute

/-!
# Spectra of indexed products

This file owns restriction from an indexed product of rings to a subproduct and the induced
closed immersion of spectra.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.Scheme.ProductSpectrum

/-- The spectrum of an indexed product of rings. -/
@[stacks 03DP]
noncomputable abbrev family {ι : Type u} (R : ι → CommRingCat.{v}) : Scheme.{max u v} :=
  Spec (CommRingCat.of ((i : ι) → R i))

/-- The spectrum of the product over the indices in `J`. -/
@[stacks 03DP]
noncomputable abbrev subfamily {ι : Type u} (R : ι → CommRingCat.{v})
    (J : Set ι) : Scheme.{max u v} :=
  Spec (CommRingCat.of ((j : J) → R j))

/-- Restriction from the full product of rings to the subproduct indexed by `J`. -/
@[stacks 03DP "restriction to a product subfamily"]
def restriction {ι : Type u} (R : ι → CommRingCat.{v}) (J : Set ι) :
    ((i : ι) → R i) →+* ((j : J) → R j) :=
  RingHom.pi fun j : J ↦ Pi.evalRingHom (fun i ↦ R i) j.1

/-- Restriction evaluates an ambient tuple at the underlying subfamily index. -/
@[simp, stacks 03DP "product-spectrum restriction component"]
theorem restriction_apply {ι : Type u} (R : ι → CommRingCat.{v})
    (J : Set ι) (x : (i : ι) → R i) (j : J) :
    restriction R J x j = x j.1 := sorry

/-- Restriction from a product to a subproduct is surjective. -/
@[stacks 03DP "product-spectrum restriction surjectivity"]
theorem restriction_surjective {ι : Type u} (R : ι → CommRingCat.{v}) (J : Set ι) :
    Function.Surjective (restriction R J) := sorry

/-- The canonical morphism from the spectrum of a subproduct to the spectrum of the ambient
product. -/
@[stacks 03DP "inclusion of a product-spectrum subfamily"]
noncomputable abbrev inclusion {ι : Type u} (R : ι → CommRingCat.{v}) (J : Set ι) :
    subfamily R J ⟶ family R :=
  Spec.map (CommRingCat.ofHom (restriction R J))

/-- The spectrum of a subproduct is a closed subscheme of the spectrum of the full product. -/
@[stacks 03DP "closed immersion of a product-spectrum subfamily"]
instance inclusion_isClosedImmersion {ι : Type u} (R : ι → CommRingCat.{v})
    (J : Set ι) : IsClosedImmersion (inclusion R J) := sorry

/-- The factors met by a morphism into the spectrum of an indexed product. -/
@[stacks 03DP "support in a product spectrum"]
def support {ι : Type u} (R : ι → CommRingCat.{v})
    {X : Scheme.{max u v}} (f : X ⟶ family R) : Set ι :=
  {i | ∃ x : X, ∃ y : subfamily R ({i} : Set ι),
    f.base x = (inclusion R ({i} : Set ι)).base y}

/-- An index belongs to the support exactly when the image meets its singleton factor. -/
@[stacks 03DP "product-spectrum support membership"]
theorem mem_support_iff {ι : Type u} (R : ι → CommRingCat.{v})
    {X : Scheme.{max u v}} (f : X ⟶ family R) (i : ι) :
    i ∈ support R f ↔ ∃ x : X, ∃ y : subfamily R ({i} : Set ι),
      f.base x = (inclusion R ({i} : Set ι)).base y := sorry

/-- Precomposition by a morphism surjective on points does not change product-spectrum
support. -/
@[stacks 03DP "product-spectrum support under surjective precomposition"]
theorem support_comp_of_surjective {ι : Type u} (R : ι → CommRingCat.{v})
    {X Y : Scheme.{max u v}} (g : Y ⟶ X) (f : X ⟶ family R)
    (h_surjective : Function.Surjective g.base) :
    support R (g ≫ f) = support R f := sorry

/-- Replacing the source by an isomorphic scheme does not change product-spectrum support. -/
@[simp, stacks 03DP "product-spectrum support under source isomorphism"]
theorem support_iso_hom {ι : Type u} (R : ι → CommRingCat.{v})
    {X Y : Scheme.{max u v}} (e : Y ≅ X) (f : X ⟶ family R) :
    support R (e.hom ≫ f) = support R f := sorry

end AlgebraicGeometry.Scheme.ProductSpectrum
