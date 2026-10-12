/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.AffineOver
public import Mathlib.AlgebraicGeometry.AffineScheme

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.AssociatedModule

/-- Triangle identity for the algebra of functions of an affine morphism over `Spec A`. -/
theorem affineOverSpecToUnder_map_fac (A : CommRingCat.{u})
    {U V : (Spec A).AffineOverᵒᵖ} (f : U ⟶ V) :
    ((Scheme.SpecΓIdentity.app A).inv ≫ Scheme.Γ.map (op (AffineOver.obj (unop U)).hom)) ≫
        Scheme.Γ.map ((AffineOver.toScheme (Spec A)).map f.unop).op =
      (Scheme.SpecΓIdentity.app A).inv ≫ Scheme.Γ.map (op (AffineOver.obj (unop V)).hom) := sorry

/-- Global functions of an affine scheme over `Spec A`, as an object of `Under A`. -/
noncomputable def affineOverSpecToUnder (A : CommRingCat.{u}) :
    (Spec A).AffineOverᵒᵖ ⥤ Under A where
  obj U := Under.mk ((Scheme.SpecΓIdentity.app A).inv ≫ Scheme.Γ.map (op (AffineOver.obj (unop U)).hom))
  map f := Under.homMk (Scheme.Γ.map ((AffineOver.toScheme (Spec A)).map f.unop).op)
      (affineOverSpecToUnder_map_fac A f)
  map_id := sorry
  map_comp := sorry

/-- The identity morphism of `Spec A` as an affine object over itself. -/
noncomputable def affineOverSpecId (A : CommRingCat.{u}) : (Spec A).AffineOver :=
  AffineOver.mk (Spec A) (inferInstance : IsAffine (Spec A)) (𝟙 (Spec A))

/-- `Spec A / Spec A` is terminal in the affine slice. -/
noncomputable def isTerminal_affineOverSpecId (A : CommRingCat.{u}) :
    IsTerminal (affineOverSpecId A) :=
  IsTerminal.ofUniqueHom
    (fun U ↦ AffineOver.homMk U.obj.hom (Category.comp_id _))
    (fun _ _ ↦ sorry)

/-- The affine slice `(Aff / Spec A)` has a terminal object. -/
instance affineOverSpec_hasTerminal (A : CommRingCat.{u}) :
    HasTerminal (Spec A).AffineOver :=
  IsTerminal.hasTerminal (isTerminal_affineOverSpecId A)

end AlgebraicGeometry.Scheme.AssociatedModule
