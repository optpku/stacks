module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.CategoryTheory.Comma.Basic
public import Mathlib.CategoryTheory.FiberedCategory.Fibered
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import stacks_project.Chap66.Definition_66_18_1_Site

/-!
# Polynomial affine spaces and `category Λ X`

Objects of `category Λ X` are morphisms `U ⟶ A` in `Over (Spec Λ)` with `U` étale over the
algebraic space `X` and `A` a polynomial affine space over `Spec Λ`. The forgetful functor
`forget Λ X` sends such a diagram to `U` in the small étale site of `X`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Cotangent

/-- An object of `Over (Spec Λ)` is a polynomial affine space when it is isomorphic over
`Spec Λ` to `𝔸(σ; Spec Λ)` for some type `σ` of variables. -/
def isPolynomialAffine (Λ : CommRingCat.{u}) : ObjectProperty (Over (Spec Λ)) :=
  fun A ↦ ∃ σ : Type u, Nonempty (A ≅ Over.mk (𝔸(σ; Spec Λ) ↘ Spec Λ))

/-- Polynomial affine spaces over `Spec Λ` are those isomorphic over `Spec Λ` to the spectrum
of a polynomial `Λ`-algebra. -/
theorem isPolynomialAffine_iff (Λ : CommRingCat.{u}) (A : Over (Spec Λ)) :
    isPolynomialAffine Λ A ↔
      ∃ σ : Type u,
        Nonempty (A ≅ Over.mk ((AffineSpace.SpecIso σ Λ).inv ≫ (𝔸(σ; Spec Λ) ↘ Spec Λ))) :=
  sorry

/-- The full subcategory of polynomial affine spaces over `Spec Λ`. -/
abbrev PolynomialAffine (Λ : CommRingCat.{u}) := (isPolynomialAffine Λ).FullSubcategory

/-- The category `category Λ X` of morphisms from an étale `X`-scheme to a polynomial affine space
over `Spec Λ`. -/
abbrev category (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ)) :=
  Comma (smallEtaleToOver X) (isPolynomialAffine Λ).ι

/-- The forgetful functor `forget Λ X` sending a morphism `U ⟶ A` to its étale domain `U`. -/
abbrev forget (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ)) :
    category Λ X ⥤ smallEtaleSite X :=
  Comma.fst (smallEtaleToOver X) (isPolynomialAffine Λ).ι

/-- An object of `category Λ X` with étale domain `U`, polynomial affine space `A`, and
over-morphism `f`. -/
def mk {Λ : CommRingCat.{u}} {X : AlgebraicSpace (Spec Λ)} (U : smallEtaleSite X)
    (A : PolynomialAffine Λ)
    (f : (smallEtaleToOver X).obj U ⟶ (isPolynomialAffine Λ).ι.obj A) :
    category Λ X :=
  ⟨U, A, f⟩

/-- The étale domain of `mk U A f` is `U`. -/
theorem mk_forget {Λ : CommRingCat.{u}} {X : AlgebraicSpace (Spec Λ)} (U : smallEtaleSite X)
    (A : PolynomialAffine Λ)
    (f : (smallEtaleToOver X).obj U ⟶ (isPolynomialAffine Λ).ι.obj A) :
    (forget Λ X).obj (mk U A f) = U :=
  sorry

/-- The object of `category Λ X` given by an étale domain `U` and a morphism to the standard
affine space `𝔸(σ; Spec Λ)`. -/
def ofAffineSpace {Λ : CommRingCat.{u}} {X : AlgebraicSpace (Spec Λ)} (U : smallEtaleSite X)
    (σ : Type u) (f : (smallEtaleToOver X).obj U ⟶ Over.mk (𝔸(σ; Spec Λ) ↘ Spec Λ)) :
    category Λ X :=
  mk U ⟨Over.mk (𝔸(σ; Spec Λ) ↘ Spec Λ), ⟨σ, ⟨Iso.refl _⟩⟩⟩ f

/-- The étale domain of `ofAffineSpace U σ f` is `U`. -/
theorem ofAffineSpace_forget {Λ : CommRingCat.{u}} {X : AlgebraicSpace (Spec Λ)}
    (U : smallEtaleSite X) (σ : Type u)
    (f : (smallEtaleToOver X).obj U ⟶ Over.mk (𝔸(σ; Spec Λ) ↘ Spec Λ)) :
    (forget Λ X).obj (ofAffineSpace U σ f) = U :=
  sorry

/-- The forgetful functor evaluates on objects to the étale domain. -/
theorem forget_obj {Λ : CommRingCat.{u}} {X : AlgebraicSpace (Spec Λ)} (x : category Λ X) :
    (forget Λ X).obj x = x.left :=
  sorry

/-- The forgetful functor evaluates on morphisms to the étale component. -/
theorem forget_map {Λ : CommRingCat.{u}} {X : AlgebraicSpace (Spec Λ)} {x y : category Λ X}
    (φ : x ⟶ y) : (forget Λ X).map φ = φ.left :=
  sorry

/-- The cartesian lift of `f : U' ⟶ forget.obj x` obtained by composing `U' ⟶ U ⟶ A`,
keeping the polynomial affine space of `x` fixed. -/
def restrict {Λ : CommRingCat.{u}} {X : AlgebraicSpace (Spec Λ)} (x : category Λ X)
    {U' : smallEtaleSite X} (f : U' ⟶ (forget Λ X).obj x) : category Λ X where
  left := U'
  right := x.right
  hom := (smallEtaleToOver X).map f ≫ x.hom

/-- The étale domain of `restrict x f` is the domain of `f`. -/
theorem restrict_forget {Λ : CommRingCat.{u}} {X : AlgebraicSpace (Spec Λ)} (x : category Λ X)
    {U' : smallEtaleSite X} (f : U' ⟶ (forget Λ X).obj x) :
    (forget Λ X).obj (restrict x f) = U' :=
  sorry

/-- Restriction keeps the polynomial affine space of `x`. -/
theorem restrict_right {Λ : CommRingCat.{u}} {X : AlgebraicSpace (Spec Λ)} (x : category Λ X)
    {U' : smallEtaleSite X} (f : U' ⟶ (forget Λ X).obj x) :
    (restrict x f).right = x.right :=
  sorry

/-- The comparison morphism `restrict x f ⟶ x` over `f`, identity on the affine space. -/
def restrictHom {Λ : CommRingCat.{u}} {X : AlgebraicSpace (Spec Λ)} (x : category Λ X)
    {U' : smallEtaleSite X} (f : U' ⟶ (forget Λ X).obj x) : restrict x f ⟶ x where
  left := f
  right := 𝟙 x.right

/-- The étale component of `restrictHom x f` is `f`. -/
theorem restrictHom_left {Λ : CommRingCat.{u}} {X : AlgebraicSpace (Spec Λ)} (x : category Λ X)
    {U' : smallEtaleSite X} (f : U' ⟶ (forget Λ X).obj x) :
    (restrictHom x f).left = f :=
  sorry

/-- The comparison `restrictHom x f` is strongly cartesian over `f`. -/
instance restrictHom_isStronglyCartesian {Λ : CommRingCat.{u}} {X : AlgebraicSpace (Spec Λ)}
    (x : category Λ X) {U' : smallEtaleSite X} (f : U' ⟶ (forget Λ X).obj x) :
    (forget Λ X).IsStronglyCartesian f (restrictHom x f) :=
  sorry

/-- The forgetful functor `forget Λ X` exhibits `category Λ X` as fibered over the small
étale site of `X`. -/
instance forget_isFibered (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ)) :
    (forget Λ X).IsFibered :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Cotangent
