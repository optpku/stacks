/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Spec
public import ReasLib.AlgebraicGeometry.Scheme.Spec.IdealSubobject
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IdealSheaf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.IdealPower
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.UniverseLift
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IdealSubobject.Pullback

/-!
# Ideal-power products from an affine ideal

An ideal `I ⊆ A` determines the closed immersion `Spec(A ⧸ I) ⟶ Spec A` as a
morphism of algebraic spaces, the inverse-image ideal `I 𝒪_X`, and the products
`I^n F`. Homogeneous multiplication by an element of `I^m` is the corresponding
global-section action, factored through the product filtration.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology

variable {A : Type u} [CommRing A]

/-- The closed immersion `Spec(A ⧸ I) ⟶ Spec A`, as a morphism of algebraic spaces over
`Spec A`. -/
def affineQuotient (I : Ideal A) :
    ofOver (Over.mk (Spec.quotientMap (R := CommRingCat.of A) I)) ⟶
      ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A)))) :=
  ofOverHomMk (Spec.quotientMap (R := CommRingCat.of A) I) (Category.comp_id _)

/-- `affineQuotient I` is `ofOverHomMk` of the affine quotient closed immersion. -/
theorem affineQuotient_eq (I : Ideal A) :
    affineQuotient I =
      ofOverHomMk (Spec.quotientMap (R := CommRingCat.of A) I) (Category.comp_id _) :=
  sorry

/-- The quasi-coherent ideal sheaf `I 𝒪_{Spec A}` associated to the closed immersion
`Spec(A ⧸ I) ⟶ Spec A`. -/
def affineIdeal (I : Ideal A) :
    IdealSubobject (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) :=
  Hom.idealSheafSubobject (affineQuotient I)

/-- `affineIdeal I` is the kernel ideal sheaf of `affineQuotient I`. -/
theorem affineIdeal_eq (I : Ideal A) :
    affineIdeal I = Hom.idealSheafSubobject (affineQuotient I) :=
  sorry

variable {X : AlgebraicSpace (Spec (CommRingCat.of A))}

/-- The image of an element of `A` as a local section of `𝒪_X` on an étale object, via the
structure morphism to `Spec A`. -/
def structureSectionApp (a : A) (U : (smallEtaleSite X)ᵒᵖ) :
    (structureSheaf X).obj.obj U :=
  ((forget₂ CommRingCat RingCat).map
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
        ((smallEtaleToOver X).obj U.unop).hom.appTop)).hom a

/-- `structureSectionApp a U` is the image of `a` under the composite of `ΓSpecIso` with the
structure map of the étale object. -/
theorem structureSectionApp_eq (a : A) (U : (smallEtaleSite X)ᵒᵖ) :
    structureSectionApp a U =
      ((forget₂ CommRingCat RingCat).map
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
            ((smallEtaleToOver X).obj U.unop).hom.appTop)).hom a :=
  sorry

/-- Restriction of `structureSectionApp a` along a morphism of étale objects. -/
theorem structureSectionApp_map (a : A) {U V : (smallEtaleSite X)ᵒᵖ} (i : U ⟶ V) :
    (structureSheaf X).obj.map i (structureSectionApp a U) = structureSectionApp a V :=
  sorry

/-- Multiplication by an element of `A` on an `𝒪_X`-module, acting sectionwise. -/
def sectionMul (F : X.Modules) (a : A) : F ⟶ F :=
  ⟨{ app := fun U ↦
      ModuleCat.ofHom
        { toFun := fun x ↦ structureSectionApp a U • x
          map_add' := sorry
          map_smul' := sorry }
     naturality := sorry }⟩

/-- Evaluating `sectionMul a` on an étale object is scalar multiplication by
`structureSectionApp a`. -/
theorem sectionMul_app (F : X.Modules) (a : A) (U : (smallEtaleSite X)ᵒᵖ)
    (x : F.val.obj U) :
    (sectionMul F a).val.app U x = structureSectionApp a U • x :=
  sorry

/-- The inverse-image ideal sheaf `I 𝒪_X`. -/
def pullbackIdeal (I : Ideal A) (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) :
    IdealSubobject X :=
  (affineIdeal I).pullback f

/-- `pullbackIdeal I f` is the inverse image of `affineIdeal I` along `f`. -/
theorem pullbackIdeal_eq (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) :
    pullbackIdeal I f = (affineIdeal I).pullback f :=
  sorry

/-- The product subobject `I^n F` of an `𝒪_X`-module. -/
noncomputable abbrev product (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules) (n : ℕ) :
    Subobject F :=
  idealPowerProductSubobject (pullbackIdeal I f) F n

/-- `product I f F n` is the ideal-power product of `pullbackIdeal I f` with `F`. -/
theorem product_eq (I : Ideal A) (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A)))))
    (F : X.Modules) (n : ℕ) :
    product I f F n = idealPowerProductSubobject (pullbackIdeal I f) F n :=
  sorry

/-- Homogeneous multiplication by `a ∈ I^m` sends `I^n F` into `I^{m+n} F`. -/
theorem actionMap_factors (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    {m n : ℕ} (a : (I ^ m : Ideal A)) :
    (product I f F (m + n)).Factors
      ((product I f F n).arrow ≫ sectionMul F a.1) :=
  sorry

/-- The degree-`m` coefficient action `I^n F ⟶ I^{m+n} F`. -/
def actionMap (I : Ideal A) (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A)))))
    (F : X.Modules) {m n : ℕ} (a : (I ^ m : Ideal A)) :
    (product I f F n : X.Modules) ⟶ (product I f F (m + n) : X.Modules) :=
  (product I f F (m + n)).factorThru
    ((product I f F n).arrow ≫ sectionMul F a.1) (actionMap_factors I f F a)

/-- The homogeneous action followed by the target inclusion is multiplication by the
corresponding global coefficient. -/
theorem actionMap_arrow (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    {m n : ℕ} (a : (I ^ m : Ideal A)) :
    actionMap I f F a ≫ (product I f F (m + n)).arrow =
      (product I f F n).arrow ≫ sectionMul F a.1 :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology
