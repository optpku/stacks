module

public import ReasLib.AlgebraicGeometry.Scheme.Coproduct.Subfamily
public import ReasLib.AlgebraicGeometry.Scheme.ProductSpectrum
public import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite product spectra as coproducts

This bridge compares a finite same-universe product spectrum with mathlib's canonical coproduct
of the factor spectra. The universe-polymorphic product-spectrum owner remains independent of
coproducts.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.ProductSpectrum

variable {ι : Type u} (R : ι → CommRingCat.{u})

/-- The subfamily coproduct inclusion and the subproduct-spectrum inclusion commute with
mathlib's canonical `sigmaSpec` comparison. -/
@[stacks 03DP "subfamily comparison"]
theorem coproductInclusion_sigmaSpec (J : Set ι) :
    Coproduct.inclusion (fun i ↦ Spec (R i)) J ≫ sigmaSpec R =
      sigmaSpec (fun j : J ↦ R j) ≫ inclusion R J := sorry

/-- For a finite family, mathlib's canonical `sigmaSpec` morphism as an isomorphism from the
coproduct of the factor spectra to the product spectrum. -/
@[stacks 03DP "finite product spectrum comparison"]
noncomputable def sigmaSpecIso [Finite ι] :
    (∐ fun i ↦ Spec (R i)) ≅ family R :=
  asIso (sigmaSpec R)

namespace sigmaSpecIso

/-- The finite `sigmaSpec` isomorphism restricted to a chosen subfamily. -/
@[stacks 03DP "finite subfamily spectrum comparison"]
noncomputable abbrev subfamily (J : Set ι) [Finite J] :
    Coproduct.subfamily (fun i ↦ Spec (R i)) J ≅ ProductSpectrum.subfamily R J :=
  ProductSpectrum.sigmaSpecIso (fun j : J ↦ R j)

/-- The full-family and subfamily `sigmaSpec` isomorphisms intertwine their canonical
inclusions. -/
@[stacks 03DP "subfamily inclusion under the finite spectrum comparison"]
theorem inclusion [Finite ι] (J : Set ι) :
    Coproduct.inclusion (fun i ↦ Spec (R i)) J ≫
        (ProductSpectrum.sigmaSpecIso R).hom =
      (subfamily R J).hom ≫ ProductSpectrum.inclusion R J := sorry

end sigmaSpecIso

/-- The order isomorphism on scheme subobjects induced by the finite `sigmaSpec`
identification. -/
@[stacks 03DP "subobjects under the finite spectrum comparison"]
noncomputable def subobjectOrderIso [Finite ι] :
    Subobject (∐ fun i ↦ Spec (R i)) ≃o Subobject (family R) :=
  Subobject.mapIsoToOrderIso (sigmaSpecIso R)

/-- For a finite family, transport a morphism to a product spectrum across the canonical
`sigmaSpec` isomorphism to the corresponding coproduct. -/
@[stacks 03DP "morphism transport to coproduct"]
noncomputable abbrev toCoproduct [Finite ι] {X : Scheme.{u}}
    (f : X ⟶ family R) : X ⟶ ∐ fun i ↦ Spec (R i) :=
  f ≫ (sigmaSpecIso R).inv

/-- Transporting the subobject represented by `f` back across `sigmaSpecIso` is represented by
the transported morphism `toCoproduct R f`. -/
@[simp, stacks 03DP "inverse subobject transport"]
theorem subobjectOrderIso_symm_mk [Finite ι] {X : Scheme.{u}}
    (f : X ⟶ family R) [Mono f] :
    (subobjectOrderIso R).symm (Subobject.mk f) =
      Subobject.mk (toCoproduct R f) := sorry

/-- The forward transport of a coproduct subobject is represented by the corresponding morphism
to the product spectrum. -/
@[simp, stacks 03DP "forward subobject transport"]
theorem subobjectOrderIso_mk [Finite ι] {X : Scheme.{u}}
    (f : X ⟶ ∐ fun i ↦ Spec (R i)) [Mono f] :
    subobjectOrderIso R (Subobject.mk f) =
      Subobject.mk (f ≫ (sigmaSpecIso R).hom) := sorry

/-- Transport to the coproduct followed by `sigmaSpec` recovers the original morphism. -/
@[reassoc (attr := simp), stacks 03DP "transport to coproduct"]
theorem toCoproduct_sigmaSpec [Finite ι] {X : Scheme.{u}}
    (f : X ⟶ family R) : toCoproduct R f ≫ sigmaSpec R = f := sorry

/-- The support of a morphism to a finite product spectrum agrees with the support obtained
after transport to the coproduct of the factor spectra. -/
@[stacks 03DP "support transport to coproduct"]
theorem coproduct_support_toCoproduct [Finite ι] {X : Scheme.{u}}
    (f : X ⟶ family R) :
    Coproduct.support (fun i ↦ Spec (R i)) (toCoproduct R f) = support R f := sorry

end AlgebraicGeometry.Scheme.ProductSpectrum
