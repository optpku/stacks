/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.LocallyInjective
public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Explicit descent along a local isomorphism

The output section is the sheaf amalgamation of the images of actual local
preimages. It is not selected from an assertion that an inverse map or an
isomorphism exists. The local restriction and factorization formulas pin the
result independently of local choices.
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u v w

namespace CategoryTheory.Presheaf.LocalIsoDescent

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable {P U F : Cᵒᵖ ⥤ Type w} (η : P ⟶ U) (g : P ⟶ F)
variable [hηs : Presheaf.IsLocallySurjective J η] [hηi : Presheaf.IsLocallyInjective J η]
variable (hF : Presheaf.IsSheaf J F)

/-- Local preimages are sent through the given morphism, on their actual image sieve. -/
def family {T : Cᵒᵖ} (x : U.obj T) :
    Presieve.FamilyOfElements F (Presheaf.imageSieve η x).arrows :=
  (Presieve.FamilyOfElements.localPreimage η x).map g

include hF hηs hηi

/-- Local injectivity of `η` and separation of `F` make the sent family compatible. -/
theorem family_compatible {T : Cᵒᵖ} (x : U.obj T) :
    (family η g x).Compatible :=
  sorry

/-- The unique sheaf amalgamation of the actual local images. -/
def app {T : Cᵒᵖ} (x : U.obj T) : F.obj T :=
  ((isSheaf_iff_isSheaf_of_type J F).mp hF _ (Presheaf.imageSieve_mem J η x)).amalgamate
    (family η g x) (family_compatible J η g hF x)

/-- On every local lift the descended section has the prescribed value. -/
theorem app_restrict {T : Cᵒᵖ} (x : U.obj T) {V : C}
    (f : V ⟶ T.unop) (hf : Presheaf.imageSieve η x f) :
    F.map f.op (app J η g hF x) =
      g.app (op V) (Presheaf.localPreimage η x f hf) :=
  Presieve.IsSheafFor.valid_glue _ (family_compatible J η g hF x) f hf

/-- Restriction commutes with this amalgamation by uniqueness of sheaf gluing. -/
theorem app_natural {T V : Cᵒᵖ} (f : T ⟶ V) (x : U.obj T) :
    F.map f (app J η g hF x) = app J η g hF (U.map f x) :=
  sorry

/-- Descent is the natural transformation whose components are the explicit amalgamations. -/
def descend : U ⟶ F where
  app T := TypeCat.ofHom (app J η g hF)
  naturality T V f := by
    ext x
    exact (app_natural J η g hF f x).symm

/-- The constructed descent agrees with the given map on the original presheaf. -/
theorem descend_fac : η ≫ descend J η g hF = g :=
  sorry

/-- A morphism into a sheaf is determined by its values on a locally surjective cover. -/
theorem hom_ext (f₁ f₂ : U ⟶ F) (h : η ≫ f₁ = η ≫ f₂) : f₁ = f₂ :=
  sorry

end CategoryTheory.Presheaf.LocalIsoDescent
