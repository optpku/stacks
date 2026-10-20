/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.AffineOver
public import Mathlib.AlgebraicGeometry.AffineScheme

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.AffineOver

/-- Global functions of an affine scheme over `Spec A`, with their structure map from `A`. -/
def toUnderObj (A : CommRingCat.{u}) (U : (Spec A).AffineOverᵒᵖ) : Under A :=
  Under.mk ((Scheme.SpecΓIdentity.app A).inv ≫ Scheme.Γ.map (op (obj (unop U)).hom))

/-- Pullback of global functions respects the structure maps from `A`. -/
theorem toUnder_map_fac (A : CommRingCat.{u})
    {U V : (Spec A).AffineOverᵒᵖ} (f : U ⟶ V) :
    ((Scheme.SpecΓIdentity.app A).inv ≫ Scheme.Γ.map (op (obj (unop U)).hom)) ≫
        Scheme.Γ.map ((toScheme (Spec A)).map f.unop).op =
      (Scheme.SpecΓIdentity.app A).inv ≫ Scheme.Γ.map (op (obj (unop V)).hom) := sorry

/-- An affine morphism over `Spec A` induces an `A`-algebra morphism on global functions. -/
def toUnderMap (A : CommRingCat.{u}) {U V : (Spec A).AffineOverᵒᵖ} (f : U ⟶ V) :
    toUnderObj A U ⟶ toUnderObj A V :=
  Under.homMk (Scheme.Γ.map ((toScheme (Spec A)).map f.unop).op) (toUnder_map_fac A f)

/-- The coordinate-algebra morphism of an identity is the identity. -/
theorem toUnder_map_id (A : CommRingCat.{u}) (U : (Spec A).AffineOverᵒᵖ) :
    toUnderMap A (𝟙 U) = 𝟙 (toUnderObj A U) := sorry

/-- Coordinate-algebra morphisms preserve composition in the opposite affine slice. -/
theorem toUnder_map_comp (A : CommRingCat.{u}) {U V W : (Spec A).AffineOverᵒᵖ}
    (f : U ⟶ V) (g : V ⟶ W) :
    toUnderMap A (f ≫ g) = toUnderMap A f ≫ toUnderMap A g := sorry

/-- The contravariant coordinate-algebra functor on affine schemes over `Spec A`. -/
def toUnder (A : CommRingCat.{u}) : (Spec A).AffineOverᵒᵖ ⥤ Under A where
  obj := toUnderObj A
  map := toUnderMap A
  map_id := toUnder_map_id A
  map_comp := toUnder_map_comp A

/-- The identity morphism of `Spec A`, viewed as an affine scheme over itself. -/
def specId (A : CommRingCat.{u}) : (Spec A).AffineOver :=
  mk (Spec A) (inferInstance : IsAffine (Spec A)) (𝟙 (Spec A))

/-- Every morphism to the identity affine scheme is its source's structure morphism. -/
theorem specId_hom_unique (A : CommRingCat.{u}) (U : (Spec A).AffineOver)
    (f : U ⟶ specId A) :
    f = homMk U.obj.hom (Category.comp_id _) := sorry

/-- The identity affine scheme over `Spec A` is terminal, with canonical structure maps. -/
def isTerminal_specId (A : CommRingCat.{u}) : IsTerminal (specId A) :=
  IsTerminal.ofUniqueHom (fun U ↦ homMk U.obj.hom (Category.comp_id _))
    (specId_hom_unique A)

end AlgebraicGeometry.Scheme.AffineOver
