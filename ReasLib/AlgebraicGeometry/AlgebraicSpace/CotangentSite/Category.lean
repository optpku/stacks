/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.CategoryTheory.Comma.Basic
public import Mathlib.CategoryTheory.FiberedCategory.Fibered
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Presentation

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Cotangent

/-- A scheme over `Spec Λ` is polynomial affine if it is isomorphic over the base to an
affine space on a set of variables. -/
def isPolynomialAffine (Λ : CommRingCat.{u}) : ObjectProperty (Over (Spec Λ)) :=
  fun A ↦ ∃ σ : Type u, Nonempty (A ≅ Over.mk (𝔸(σ; Spec Λ) ↘ Spec Λ))

/-- Polynomial affineness is equivalently an isomorphism with the spectrum of a polynomial
algebra over `Λ`. -/
theorem isPolynomialAffine_iff (Λ : CommRingCat.{u}) (A : Over (Spec Λ)) :
    isPolynomialAffine Λ A ↔
      ∃ σ : Type u,
        Nonempty (A ≅ Over.mk ((AffineSpace.SpecIso σ Λ).inv ≫ (𝔸(σ; Spec Λ) ↘ Spec Λ))) := by
  constructor
  · rintro ⟨σ, ⟨e⟩⟩
    exact ⟨σ, ⟨e ≪≫ Over.isoMk (AffineSpace.SpecIso σ Λ)
      (by exact (AffineSpace.SpecIso σ Λ).hom_inv_id_assoc _)⟩⟩
  · rintro ⟨σ, ⟨e⟩⟩
    exact ⟨σ, ⟨e ≪≫ Over.isoMk (AffineSpace.SpecIso σ Λ).symm (by rfl)⟩⟩

/-- The full category of polynomial affine schemes over `Spec Λ`. -/
abbrev PolynomialAffine (Λ : CommRingCat.{u}) := (isPolynomialAffine Λ).FullSubcategory

/-- The category of étale charts of `X` equipped with a map to a polynomial affine scheme
over `Spec Λ`. -/
abbrev category (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ)) :=
  Comma (smallEtaleToOver X) (isPolynomialAffine Λ).ι

/-- The projection from polynomial affine presentations to the small étale site. -/
abbrev forget (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ)) :
    category Λ X ⥤ smallEtaleSite X :=
  Comma.fst (smallEtaleToOver X) (isPolynomialAffine Λ).ι

/-- An étale chart and its map over the base to a polynomial affine scheme define a
polynomial affine presentation. -/
def mk {Λ : CommRingCat.{u}} {X : AlgebraicSpace (Spec Λ)} (U : smallEtaleSite X)
    (A : PolynomialAffine Λ)
    (f : (smallEtaleToOver X).obj U ⟶ (isPolynomialAffine Λ).ι.obj A) : category Λ X :=
  ⟨U, A, f⟩

/-- The projection of a constructed presentation is its specified étale chart. -/
theorem mk_forget {Λ : CommRingCat.{u}} {X : AlgebraicSpace (Spec Λ)} (U : smallEtaleSite X)
    (A : PolynomialAffine Λ)
    (f : (smallEtaleToOver X).obj U ⟶ (isPolynomialAffine Λ).ι.obj A) :
    (forget Λ X).obj (mk U A f) = U := rfl

/-- A map from an étale chart to an affine space defines a polynomial affine presentation. -/
def ofAffineSpace {Λ : CommRingCat.{u}} {X : AlgebraicSpace (Spec Λ)} (U : smallEtaleSite X)
    (σ : Type u) (f : (smallEtaleToOver X).obj U ⟶ Over.mk (𝔸(σ; Spec Λ) ↘ Spec Λ)) :
    category Λ X :=
  mk U ⟨Over.mk (𝔸(σ; Spec Λ) ↘ Spec Λ), ⟨σ, ⟨Iso.refl _⟩⟩⟩ f

/-- A presentation with an affine-space target projects to its specified étale chart. -/
theorem ofAffineSpace_forget {Λ : CommRingCat.{u}} {X : AlgebraicSpace (Spec Λ)}
    (U : smallEtaleSite X) (σ : Type u)
    (f : (smallEtaleToOver X).obj U ⟶ Over.mk (𝔸(σ; Spec Λ) ↘ Spec Λ)) :
    (forget Λ X).obj (ofAffineSpace U σ f) = U := rfl

/-- The projection of a presentation is its chart component. -/
theorem forget_obj {Λ : CommRingCat.{u}} {X : AlgebraicSpace (Spec Λ)} (x : category Λ X) :
    (forget Λ X).obj x = x.left := rfl

/-- The projection of a morphism of presentations is its chart morphism. -/
theorem forget_map {Λ : CommRingCat.{u}} {X : AlgebraicSpace (Spec Λ)} {x y : category Λ X}
    (φ : x ⟶ y) : (forget Λ X).map φ = φ.left := rfl

/-- Restriction of a presentation along a morphism of étale charts keeps its polynomial
affine target and composes the chart map. -/
def restrict {Λ : CommRingCat.{u}} {X : AlgebraicSpace (Spec Λ)} (x : category Λ X)
    {U' : smallEtaleSite X} (f : U' ⟶ (forget Λ X).obj x) : category Λ X where
  left := U'
  right := x.right
  hom := (smallEtaleToOver X).map f ≫ x.hom

/-- A restricted presentation projects to the new étale chart. -/
theorem restrict_forget {Λ : CommRingCat.{u}} {X : AlgebraicSpace (Spec Λ)} (x : category Λ X)
    {U' : smallEtaleSite X} (f : U' ⟶ (forget Λ X).obj x) :
    (forget Λ X).obj (restrict x f) = U' := rfl

/-- Restriction preserves the polynomial affine target. -/
theorem restrict_right {Λ : CommRingCat.{u}} {X : AlgebraicSpace (Spec Λ)} (x : category Λ X)
    {U' : smallEtaleSite X} (f : U' ⟶ (forget Λ X).obj x) :
    (restrict x f).right = x.right := rfl

/-- The canonical morphism from a restricted presentation to the original presentation. -/
def restrictHom {Λ : CommRingCat.{u}} {X : AlgebraicSpace (Spec Λ)} (x : category Λ X)
    {U' : smallEtaleSite X} (f : U' ⟶ (forget Λ X).obj x) : restrict x f ⟶ x where
  left := f
  right := 𝟙 x.right

/-- The chart component of the restriction morphism is the given chart morphism. -/
theorem restrictHom_left {Λ : CommRingCat.{u}} {X : AlgebraicSpace (Spec Λ)}
    (x : category Λ X) {U' : smallEtaleSite X} (f : U' ⟶ (forget Λ X).obj x) :
    (restrictHom x f).left = f := rfl

/-- Restriction morphisms are strongly cartesian over the small étale site. -/
instance restrictHom_isStronglyCartesian {Λ : CommRingCat.{u}} {X : AlgebraicSpace (Spec Λ)}
    (x : category Λ X) {U' : smallEtaleSite X} (f : U' ⟶ (forget Λ X).obj x) :
    (forget Λ X).IsStronglyCartesian f (restrictHom x f) where
  toIsHomLift := IsHomLift.map (forget Λ X) (restrictHom x f)
  universal_property' := by
    intro y g φ hφ
    have hleft : g ≫ f = φ.left :=
      IsHomLift.eq_of_isHomLift (forget Λ X) (g ≫ f) φ
    let χ : y ⟶ restrict x f :=
      { left := g
        right := φ.right
        w := by
          change (smallEtaleToOver X).map g ≫
              ((smallEtaleToOver X).map f ≫ x.hom) =
            y.hom ≫ (isPolynomialAffine Λ).ι.map φ.right
          rw [← Category.assoc, ← Functor.map_comp, hleft]
          exact φ.w }
    refine ⟨χ, ⟨IsHomLift.map (forget Λ X) χ, ?_⟩, ?_⟩
    · show χ ≫ restrictHom x f = φ
      apply Comma.hom_ext
      · change g ≫ f = φ.left
        exact hleft
      · change φ.right ≫ 𝟙 x.right = φ.right
        exact Category.comp_id _
    · intro ψ hψ
      apply Comma.hom_ext
      · change ψ.left = g
        exact (@IsHomLift.eq_of_isHomLift _ _ _ _ (forget Λ X)
          _ _ g ψ hψ.1).symm
      · change ψ.right = φ.right
        have hright := congrArg CommaMorphism.right hψ.2
        change ψ.right ≫ 𝟙 x.right = φ.right at hright
        exact (Category.comp_id ψ.right).symm.trans hright

/-- Polynomial affine presentations form a fibered category over the small étale site. -/
instance forget_isFibered (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ)) :
    (forget Λ X).IsFibered := by
  apply Functor.IsFibered.of_exists_isStronglyCartesian
  intro x U' f
  exact ⟨restrict x f, restrictHom x f, inferInstance⟩

end AlgebraicGeometry.AlgebraicSpace.Cotangent
