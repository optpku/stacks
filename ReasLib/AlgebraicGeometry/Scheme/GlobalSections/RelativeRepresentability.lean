/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import ReasLib.AlgebraicGeometry.Scheme.Sites.StructureSheaf

/-!
# Relative representability of global sections

The underlying Type-valued structure presheaf on schemes over a base is represented by the
relative affine line.
-/

@[expose] public section

open CategoryTheory Opposite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Over.GlobalSections

/-- The Type-valued global-sections presheaf on schemes over `S`. -/
def functor (S : Scheme.{u}) : (CategoryTheory.Over S)ᵒᵖ ⥤ Type u :=
  Scheme.Site.structurePresheaf (CategoryTheory.Over.forget S) ⋙
    CategoryTheory.forget RingCat

/-- Evaluation of the relative global-sections functor at `U` is `Γ(U.left, ⊤)`. -/
theorem functor_obj (S : Scheme.{u}) (U : CategoryTheory.Over S) :
    (functor S).obj (op U) = Γ(U.left, ⊤) := sorry

/-- The relative affine line, regarded as a scheme over `S`. -/
abbrev affineLine (S : Scheme.{u}) : CategoryTheory.Over S :=
  CategoryTheory.Over.mk (𝔸(ULift.{u} (Fin 1); S) ↘ S)

/-- The underlying scheme of the relative affine line is `𝔸¹_S`. -/
theorem affineLine_left (S : Scheme.{u}) :
    (affineLine S).left = 𝔸(ULift.{u} (Fin 1); S) := sorry

/-- The structure morphism of the relative affine line is the canonical projection to `S`. -/
theorem affineLine_hom (S : Scheme.{u}) :
    (affineLine S).hom = 𝔸(ULift.{u} (Fin 1); S) ↘ S := sorry

/-- A morphism over `S` to the relative affine line determines its unique coordinate section. -/
def toSection {S : Scheme.{u}} {U : CategoryTheory.Over S}
    (f : U ⟶ affineLine S) : (functor S).obj (op U) :=
  f.left.appTop (AffineSpace.coord S (ULift.up (0 : Fin 1)))

/-- The affine-space morphism associated to a section commutes with the maps to `S`. -/
theorem ofSection_over {S : Scheme.{u}} (U : CategoryTheory.Over S)
    (a : (functor S).obj (op U)) :
    AffineSpace.homOfVector U.hom (fun _ ↦ a) ≫ (affineLine S).hom = U.hom := sorry

/-- A global section on `U` determines a morphism over `S` to the relative affine line. -/
def ofSection {S : Scheme.{u}} (U : CategoryTheory.Over S)
    (a : (functor S).obj (op U)) : U ⟶ affineLine S :=
  CategoryTheory.Over.homMk (AffineSpace.homOfVector U.hom (fun _ ↦ a))
    (ofSection_over U a)

/-- Passing from a section to its affine-line morphism and back recovers the section. -/
theorem toSection_ofSection {S : Scheme.{u}} (U : CategoryTheory.Over S)
    (a : (functor S).obj (op U)) :
    toSection (ofSection U a) = a := sorry

/-- Passing from an affine-line morphism to its section and back recovers the morphism. -/
theorem ofSection_toSection {S : Scheme.{u}} (U : CategoryTheory.Over S)
    (f : U ⟶ affineLine S) :
    ofSection U (toSection f) = f := sorry

/-- Morphisms over `S` to the relative affine line are equivalent to global sections. -/
def homEquiv {S : Scheme.{u}} (U : CategoryTheory.Over S) :
    (U ⟶ affineLine S) ≃ (functor S).obj (op U) where
  toFun := toSection
  invFun := ofSection U
  left_inv := ofSection_toSection U
  right_inv := toSection_ofSection U

/-- The relative affine-line equivalence sends a slice morphism to its coordinate section. -/
theorem homEquiv_apply {S : Scheme.{u}} (U : CategoryTheory.Over S)
    (f : U ⟶ affineLine S) :
    homEquiv U f = toSection f := sorry

/-- The objectwise isomorphism identifying the Yoneda presheaf of `𝔸¹_S` with global sections. -/
def componentIso {S : Scheme.{u}} (U : (CategoryTheory.Over S)ᵒᵖ) :
    (yoneda.obj (affineLine S)).obj U ≅ (functor S).obj U :=
  (homEquiv (unop U)).toIso

/-- Naturality of the relative affine-line interpretation of global sections. -/
theorem componentIso_naturality {S : Scheme.{u}}
    {U V : (CategoryTheory.Over S)ᵒᵖ} (f : U ⟶ V) :
    (yoneda.obj (affineLine S)).map f ≫ (componentIso V).hom =
      (componentIso U).hom ≫ (functor S).map f := sorry

/-- The natural isomorphism representing relative global sections by `𝔸¹_S`. -/
def representingIso (S : Scheme.{u}) :
    yoneda.obj (affineLine S) ≅ functor S :=
  NatIso.ofComponents componentIso (fun f ↦ componentIso_naturality f)

/-- The representing isomorphism has the expected objectwise forward map. -/
theorem representingIso_hom_app (S : Scheme.{u})
    (U : (CategoryTheory.Over S)ᵒᵖ) :
    (representingIso S).hom.app U = (componentIso U).hom := sorry

/-- The relative global-sections functor is representable. -/
theorem functor_isRepresentable (S : Scheme.{u}) :
    (functor S).IsRepresentable :=
  Functor.IsRepresentable.mk' (representingIso S)

end AlgebraicGeometry.Scheme.Over.GlobalSections
