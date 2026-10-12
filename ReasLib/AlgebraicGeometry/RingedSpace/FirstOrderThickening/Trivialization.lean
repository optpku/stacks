/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening.Splitting
public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening.Hom

/-!
# Trivialized first-order thickenings of ringed spaces

A trivialization is a chosen retraction of a first-order thickening.  The
category of trivialized thickenings uses morphisms that preserve the chosen
retractions.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry.RingedSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.IsFirstOrderThickening

/-- A first-order thickening is trivial when it admits a left inverse. -/
class IsTrivial {X X' : RingedSpace.{u}} (i : X ⟶ X') [IsFirstOrderThickening i] : Prop
    extends IsSplitMono i

/-- A first-order thickening is trivial if and only if it admits a left inverse. -/
theorem isTrivial_iff {X X' : RingedSpace.{u}} (i : X ⟶ X') [IsFirstOrderThickening i] :
    IsTrivial i ↔ ∃ π : X' ⟶ X, i ≫ π = 𝟙 X := sorry

/-- A split monomorphism that is a first-order thickening is trivial. -/
instance instIsTrivial_of_isSplitMono {X X' : RingedSpace.{u}} (i : X ⟶ X')
    [IsFirstOrderThickening i] [IsSplitMono i] : IsTrivial i where

/-- A trivialization of a first-order thickening is a chosen left inverse. -/
abbrev Trivialization {X X' : RingedSpace.{u}} (i : X ⟶ X') [IsFirstOrderThickening i] :=
  SplitMono i

/-- Package a left inverse of a first-order thickening as a trivialization. -/
abbrev Trivialization.ofRetraction {X X' : RingedSpace.{u}} {i : X ⟶ X'}
    [IsFirstOrderThickening i] (π : X' ⟶ X) (hπ : i ≫ π = 𝟙 X) :
    Trivialization i :=
  ⟨π, hπ⟩

/-- The underlying continuous map of a trivialization is a homeomorphism. -/
instance instIsIso_retraction_base {X X' : RingedSpace.{u}} {i : X ⟶ X'}
    [IsFirstOrderThickening i] (τ : Trivialization i) :
    IsIso τ.retraction.hom.base := sorry

/-- A splitting of the transported structure-sheaf map. -/
def IsAlgebraSplitting {X X' : RingedSpace.{u}} (i : X ⟶ X') [IsFirstOrderThickening i]
    (σ : X.presheaf ⟶ (CategoryTheory.inv i.hom.base) _* X'.presheaf) : Prop :=
  σ ≫ (TopCat.Presheaf.pushforward CommRingCat.{u}
        (CategoryTheory.inv i.hom.base)).map i.hom.c ≫
      eqToHom
        (congrArg
          (fun f : X.carrier ⟶ X.carrier =>
            (TopCat.Presheaf.pushforward CommRingCat.{u} f).obj X.presheaf)
          (IsIso.hom_inv_id i.hom.base)) = 𝟙 X.presheaf

/-- The morphism of ringed spaces associated to a splitting. -/
def ofSplitting {X X' : RingedSpace.{u}} (i : X ⟶ X') [IsFirstOrderThickening i]
    (σ : X.presheaf ⟶ (CategoryTheory.inv i.hom.base) _* X'.presheaf) : X' ⟶ X :=
  InducedCategory.homMk
    { base := CategoryTheory.inv i.hom.base
      c := σ }

/-- The structure-sheaf component of `ofSplitting` is the given splitting. -/
theorem ofSplitting_hom_c {X X' : RingedSpace.{u}} (i : X ⟶ X')
    [IsFirstOrderThickening i]
    (σ : X.presheaf ⟶ (CategoryTheory.inv i.hom.base) _* X'.presheaf) :
    (ofSplitting i σ).hom.c = σ := sorry

/-- A splitting of the transported structure-sheaf map gives a left inverse. -/
theorem ofSplitting_leftInv {X X' : RingedSpace.{u}} (i : X ⟶ X')
    [IsFirstOrderThickening i]
    (σ : X.presheaf ⟶ (CategoryTheory.inv i.hom.base) _* X'.presheaf)
    (hσ : IsAlgebraSplitting i σ) :
    i ≫ ofSplitting i σ = 𝟙 X := sorry

/-- The type of trivialized first-order thickenings of `X`. -/
def Trivialized (X : RingedSpace.{u}) :=
  Σ' (ambient : RingedSpace.{u}),
    Σ' (inclusion : X ⟶ ambient),
      Σ' (_ : IsFirstOrderThickening inclusion), SplitMono inclusion

/-- Construct a trivialized first-order thickening from its data. -/
def Trivialized.mk {X : RingedSpace.{u}} (ambient : RingedSpace.{u})
    (inclusion : X ⟶ ambient) [h : IsFirstOrderThickening inclusion]
    (trivialization : SplitMono inclusion) : Trivialized X :=
  ⟨ambient, inclusion, h, trivialization⟩

/-- The ambient ringed space of a trivialized first-order thickening. -/
def Trivialized.ambient {X : RingedSpace.{u}} (T : Trivialized X) : RingedSpace.{u} := T.1

/-- The inclusion of the base into a trivialized first-order thickening. -/
def Trivialized.inclusion {X : RingedSpace.{u}} (T : Trivialized X) : X ⟶ T.ambient := T.2.1

/-- The first-order thickening evidence stored in a trivialized object. -/
instance Trivialized.isFirstOrder {X : RingedSpace.{u}} (T : Trivialized X) :
    IsFirstOrderThickening T.inclusion := T.2.2.1

/-- The chosen retraction of a trivialized first-order thickening. -/
def Trivialized.trivialization {X : RingedSpace.{u}} (T : Trivialized X) :
    SplitMono T.inclusion := T.2.2.2

/-- Morphisms of trivialized thickenings preserve the chosen retractions. -/
def Trivialized.Hom {X : RingedSpace.{u}} (T₁ T₂ : Trivialized X) :=
  { f : @AlgebraicGeometry.RingedSpace.IsFirstOrderThickening.Hom
        X T₁.ambient T₂.ambient T₁.inclusion T₂.inclusion
        T₁.isFirstOrder T₂.isFirstOrder //
      AlgebraicGeometry.RingedSpace.IsFirstOrderThickening.Hom.hom f ≫
        T₂.trivialization.retraction = T₁.trivialization.retraction }

/-- Package a commuting triangle with its retraction compatibility. -/
def Trivialized.Hom.mk {X : RingedSpace.{u}} {T₁ T₂ : Trivialized X}
    (f : @AlgebraicGeometry.RingedSpace.IsFirstOrderThickening.Hom
      X T₁.ambient T₂.ambient T₁.inclusion T₂.inclusion
      T₁.isFirstOrder T₂.isFirstOrder)
    (h : f.hom ≫ T₂.trivialization.retraction = T₁.trivialization.retraction) :
    Trivialized.Hom T₁ T₂ := ⟨f, h⟩

/-- The underlying first-order-thickening morphism. -/
def Trivialized.Hom.hom {X : RingedSpace.{u}} {T₁ T₂ : Trivialized X}
    (f : Trivialized.Hom T₁ T₂) :
    @AlgebraicGeometry.RingedSpace.IsFirstOrderThickening.Hom
      X T₁.ambient T₂.ambient T₁.inclusion T₂.inclusion
      T₁.isFirstOrder T₂.isFirstOrder := f.1

/-- The identity morphism of a trivialized first-order thickening. -/
def Trivialized.Hom.id {X : RingedSpace.{u}} (T : Trivialized X) :
    Trivialized.Hom T T :=
  Trivialized.Hom.mk
    (@AlgebraicGeometry.RingedSpace.IsFirstOrderThickening.Hom.id
      X T.ambient T.inclusion T.isFirstOrder)
    (by
      change (@AlgebraicGeometry.RingedSpace.IsFirstOrderThickening.Hom.id
        X T.ambient T.inclusion T.isFirstOrder).hom ≫
          T.trivialization.retraction = T.trivialization.retraction
      rw [AlgebraicGeometry.RingedSpace.IsFirstOrderThickening.Hom.id_hom]
      simp)

/-- Composition of retraction-preserving morphisms. -/
def Trivialized.Hom.comp {X : RingedSpace.{u}} {T₁ T₂ T₃ : Trivialized X}
    (f : Trivialized.Hom T₁ T₂) (g : Trivialized.Hom T₂ T₃) :
    Trivialized.Hom T₁ T₃ :=
  Trivialized.Hom.mk
    (AlgebraicGeometry.RingedSpace.IsFirstOrderThickening.Hom.comp f.hom g.hom)
    (by
      change (AlgebraicGeometry.RingedSpace.IsFirstOrderThickening.Hom.comp f.1 g.1).hom ≫
        T₃.trivialization.retraction = T₁.trivialization.retraction
      rw [AlgebraicGeometry.RingedSpace.IsFirstOrderThickening.Hom.comp_hom,
        Category.assoc, g.2, f.2])

/-- The category of trivialized first-order thickenings. -/
instance instCategoryTrivialized {X : RingedSpace.{u}} : Category (Trivialized X) where
  Hom := Trivialized.Hom
  id := Trivialized.Hom.id
  comp := @Trivialized.Hom.comp X
  id_comp := by
    intro T₁ T₂ f
    change Trivialized.Hom.comp (Trivialized.Hom.id T₁) f = f
    apply Subtype.ext
    change AlgebraicGeometry.RingedSpace.IsFirstOrderThickening.Hom.comp
      (AlgebraicGeometry.RingedSpace.IsFirstOrderThickening.Hom.id T₁.inclusion) f.1 = f.1
    simp [AlgebraicGeometry.RingedSpace.IsFirstOrderThickening.Hom.comp,
      AlgebraicGeometry.RingedSpace.IsFirstOrderThickening.Hom.id]
  comp_id := by
    intro T₁ T₂ f
    change Trivialized.Hom.comp f (Trivialized.Hom.id T₂) = f
    apply Subtype.ext
    change AlgebraicGeometry.RingedSpace.IsFirstOrderThickening.Hom.comp f.1
      (AlgebraicGeometry.RingedSpace.IsFirstOrderThickening.Hom.id T₂.inclusion) = f.1
    simp [AlgebraicGeometry.RingedSpace.IsFirstOrderThickening.Hom.comp,
      AlgebraicGeometry.RingedSpace.IsFirstOrderThickening.Hom.id]
  assoc := by
    intro T₁ T₂ T₃ T₄ f g h
    change Trivialized.Hom.comp (Trivialized.Hom.comp f g) h =
      Trivialized.Hom.comp f (Trivialized.Hom.comp g h)
    apply Subtype.ext
    change AlgebraicGeometry.RingedSpace.IsFirstOrderThickening.Hom.comp
        (AlgebraicGeometry.RingedSpace.IsFirstOrderThickening.Hom.comp f.1 g.1) h.1 =
      AlgebraicGeometry.RingedSpace.IsFirstOrderThickening.Hom.comp f.1
        (AlgebraicGeometry.RingedSpace.IsFirstOrderThickening.Hom.comp g.1 h.1)
    simp [AlgebraicGeometry.RingedSpace.IsFirstOrderThickening.Hom.comp, Category.assoc]

end AlgebraicGeometry.RingedSpace.IsFirstOrderThickening
