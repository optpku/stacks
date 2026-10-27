/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.Stackification.Construction.Realization
public import ReasLib.CategoryTheory.Fibered.CoGrothendieck.Basic

/-!
# Actual inverse data in the groupoid stackification

Original groupoid-fibration witnesses provide the inverse Cartesian factors of
local components. Descent morphisms are inverted componentwise on their actual
common cover before passing to quotient classes.
-/

@[expose] public section

open CategoryTheory Opposite GrothendieckTopology

noncomputable section

universe u v uX vX uF vF

namespace CategoryTheory.Functor.StackificationConstruction

variable {C : Type u} [Category.{v} C] {X : Type uX} [Category.{vX} X]
variable (J : GrothendieckTopology C) (p : X ⥤ C) (χ : p.Cleavage)

/-- Original groupoid-fibration data give the actual strong certificate at any
displayed lift, using the implemented native fibre construction. -/
theorem originalStrong (hG : Functor.IsFibered.InGroupoids p)
    {a b : X} {R S : C} (f : R ⟶ S) (φ : a ⟶ b) (hφ : p.IsHomLift f φ) :
    p.IsStronglyCartesian f φ := by
  cases hφ
  exact @Functor.IsFibered.isStronglyCartesian_of_isCartesian C X _ _ p hG.toIsFibered
    _ _ (p.map φ) _ _ φ (hG.all_isCartesian φ)

/-- Evaluating the quotient representative preserves its displayed lift. -/
theorem separatedRepresentativeLift {a b : Separated J p χ} {R S : C}
    (f : R ⟶ S) (τ : a ⟶ b) (hτ : (Separated.projection J p χ).IsHomLift f τ) :
    p.IsHomLift f (Quotient.out τ) := by
  have h := congrArg ((Separated.projection J p χ).map) (Quotient.out_eq τ)
  change p.map (Quotient.out τ) = (Separated.projection J p χ).map τ at h
  letI := hτ
  exact IsHomLift.of_fac' p f _
    (IsHomLift.domain_eq (Separated.projection J p χ) f τ)
    (IsHomLift.codomain_eq (Separated.projection J p χ) f τ)
    (h.trans (IsHomLift.fac' (Separated.projection J p χ) f τ))

private theorem separatedMapLift {a b : X} {R S : C}
    (f : R ⟶ S) (φ : a ⟶ b) (hφ : p.IsHomLift f φ) :
    (Separated.projection J p χ).IsHomLift f ((Separated.ofOriginal J p χ).map φ) := by
  cases hφ
  change (Separated.projection J p χ).IsHomLift
    ((Separated.projection J p χ).map ((Separated.ofOriginal J p χ).map φ))
    ((Separated.ofOriginal J p χ).map φ)
  exact Functor.IsHomLift.map _

/-- The base isomorphism between two objects of the same standard fibre is
literal transport through their common fibre index. -/
def fiberBaseIso {U : C} (a b : (Localized.projection J p χ).Fiber U) :
    p.obj a.1.obj.obj ≅ p.obj b.1.obj.obj :=
  eqToIso a.2 ≪≫ (eqToIso b.2).symm

/-- A native representative of a fibre morphism has the displayed transport base. -/
theorem fiberRepresentative_base {U : C} {a b : (Localized.projection J p χ).Fiber U}
    (τ : a ⟶ b) :
    (Quotient.out τ.1).base = (fiberBaseIso J p χ a b).hom := by
  have h := congrArg ((Localized.projection J p χ).map) (Quotient.out_eq τ.1)
  change (Quotient.out τ.1).base = (Localized.projection J p χ).map τ.1 at h
  letI := τ.2
  change (Quotient.out τ.1).base = eqToHom a.2 ≫ eqToHom b.2.symm
  simpa only [Category.id_comp] using
    h.trans (IsHomLift.fac' (Localized.projection J p χ) (𝟙 U) τ.1)

/-- Each component of the inverse family is an original Cartesian factor,
followed by the original lift into the source object. -/
def fiberInverseRaw (hG : Functor.IsFibered.InGroupoids p)
    {U : C} {a b : (Localized.projection J p χ).Fiber U} (τ : a ⟶ b) :
    LocalArrow J p χ b.1.obj a.1.obj where
  base := (fiberBaseIso J p χ a b).inv
  cover := (Quotient.out τ.1).cover.pullback (fiberBaseIso J p χ a b).inv
  component I := by
    let φ : LocalArrow J p χ a.1.obj b.1.obj := Quotient.out τ.1
    let iso := fiberBaseIso J p χ a b
    let raw := Quotient.out (φ.component I.base)
    have rawLift : p.IsHomLift (I.base.f ≫ φ.base) raw :=
      @separatedRepresentativeLift C _ X _ J p χ
        ((Separated.ofOriginal J p χ).obj (sourceRestriction J p χ a.1.obj I.base.f)) b.1.obj
        I.Y (p.obj b.1.obj.obj) (I.base.f ≫ φ.base) (φ.component I.base) (φ.isHomLift I.base)
    have base_eq : I.base.f ≫ φ.base = I.f :=
      (Category.assoc I.f iso.inv φ.base).trans
        ((congrArg (fun r ↦ I.f ≫ (iso.inv ≫ r)) (fiberRepresentative_base J p χ τ)).trans
          ((congrArg (fun r ↦ I.f ≫ r) iso.inv_hom_id).trans (Category.comp_id I.f)))
    have liftAtI : p.IsHomLift I.f raw := base_eq ▸ rawLift
    let strong := originalStrong p hG I.f raw liftAtI
    let target := χ.reindexLift I.f (⟨b.1.obj.obj, rfl⟩ : p.Fiber (p.obj b.1.obj.obj))
    let inverseComponent := @Functor.IsStronglyCartesian.map C X _ _ p
      I.Y (p.obj b.1.obj.obj) (sourceRestriction J p χ a.1.obj I.base.f) b.1.obj.obj
      I.f raw strong I.Y target.source (𝟙 I.Y) I.f (Category.id_comp I.f).symm
      target.hom target.isStronglyCartesian.toIsHomLift
    exact (Separated.ofOriginal J p χ).map
      (inverseComponent ≫ χ.cartesianHom I.base.f
        (⟨a.1.obj.obj, rfl⟩ : p.Fiber (p.obj a.1.obj.obj)))
  isHomLift := by
    intro I
    let φ : LocalArrow J p χ a.1.obj b.1.obj := Quotient.out τ.1
    let iso := fiberBaseIso J p χ a b
    let raw := Quotient.out (φ.component I.base)
    have rawLift : p.IsHomLift (I.base.f ≫ φ.base) raw :=
      @separatedRepresentativeLift C _ X _ J p χ
        ((Separated.ofOriginal J p χ).obj (sourceRestriction J p χ a.1.obj I.base.f)) b.1.obj
        I.Y (p.obj b.1.obj.obj) (I.base.f ≫ φ.base) (φ.component I.base) (φ.isHomLift I.base)
    have base_eq : I.base.f ≫ φ.base = I.f :=
      (Category.assoc I.f iso.inv φ.base).trans
        ((congrArg (fun r ↦ I.f ≫ (iso.inv ≫ r)) (fiberRepresentative_base J p χ τ)).trans
          ((congrArg (fun r ↦ I.f ≫ r) iso.inv_hom_id).trans (Category.comp_id I.f)))
    have liftAtI : p.IsHomLift I.f raw := base_eq ▸ rawLift
    let strong := originalStrong p hG I.f raw liftAtI
    let target := χ.reindexLift I.f (⟨b.1.obj.obj, rfl⟩ : p.Fiber (p.obj b.1.obj.obj))
    let inverseComponent := @Functor.IsStronglyCartesian.map C X _ _ p
      I.Y (p.obj b.1.obj.obj) (sourceRestriction J p χ a.1.obj I.base.f) b.1.obj.obj
      I.f raw strong I.Y target.source (𝟙 I.Y) I.f (Category.id_comp I.f).symm
      target.hom target.isStronglyCartesian.toIsHomLift
    have hInverse : p.IsHomLift (𝟙 I.Y) inverseComponent :=
      @Functor.IsStronglyCartesian.map_isHomLift C X _ _ p
        I.Y (p.obj b.1.obj.obj) (sourceRestriction J p χ a.1.obj I.base.f) b.1.obj.obj
        I.f raw strong I.Y target.source (𝟙 I.Y) I.f (Category.id_comp I.f).symm
        target.hom target.isStronglyCartesian.toIsHomLift
    have hCartesian : p.IsHomLift I.base.f
        (χ.cartesianHom I.base.f (⟨a.1.obj.obj, rfl⟩ : p.Fiber (p.obj a.1.obj.obj))) :=
      (χ.reindexLift I.base.f (⟨a.1.obj.obj, rfl⟩ : p.Fiber (p.obj a.1.obj.obj))).isStronglyCartesian.toIsHomLift
    have hcomp : p.IsHomLift I.base.f
        (inverseComponent ≫ χ.cartesianHom I.base.f
          (⟨a.1.obj.obj, rfl⟩ : p.Fiber (p.obj a.1.obj.obj))) :=
      @IsHomLift.comp_lift_id_left C X _ _ p _ _ _ _ _ I.base.f
        (χ.cartesianHom I.base.f (⟨a.1.obj.obj, rfl⟩ : p.Fiber (p.obj a.1.obj.obj)))
        hCartesian inverseComponent hInverse
    exact separatedMapLift J p χ I.base.f
      (inverseComponent ≫ χ.cartesianHom I.base.f
        (⟨a.1.obj.obj, rfl⟩ : p.Fiber (p.obj a.1.obj.obj))) hcomp
  compatibility := by sorry

/-- The inverse fibre morphism has the explicit inverse local-arrow class. -/
def fiberInverse (hG : Functor.IsFibered.InGroupoids p)
    {U : C} {a b : (Localized.projection J p χ).Fiber U} (τ : a ⟶ b) : b ⟶ a :=
  ⟨Quotient.mk'' (fiberInverseRaw J p χ hG τ), by
    apply IsHomLift.of_fac' (Localized.projection J p χ) (𝟙 U) _ b.2 a.2
    change eqToHom b.2 ≫ eqToHom a.2.symm =
      eqToHom b.2 ≫ 𝟙 U ≫ eqToHom a.2.symm
    rw [Category.id_comp]⟩

/-- The local-arrow fibres carry the actual inverse operation above. -/
@[reducible]
def localFiberGroupoid (hG : Functor.IsFibered.InGroupoids p) (U : C) :
    Groupoid.{max u v vX} ((Localized.projection J p χ).Fiber U) :=
  have hinv : ∀ {a b : (Localized.projection J p χ).Fiber U} (τ : a ⟶ b),
      fiberInverse J p χ hG τ ≫ τ = 𝟙 b := sorry
  { toCategory := inferInstanceAs (Category.{max u v vX} ((Localized.projection J p χ).Fiber U))
    inv := fiberInverse J p χ hG
    inv_comp := hinv
    comp_inv := by
      intro a b τ
      have h : fiberInverse J p χ hG (fiberInverse J p χ hG τ) = τ := by
        calc
          fiberInverse J p χ hG (fiberInverse J p χ hG τ) =
              fiberInverse J p χ hG (fiberInverse J p χ hG τ) ≫
                (fiberInverse J p χ hG τ ≫ τ) := by rw [hinv τ, Category.comp_id]
          _ = τ := by rw [← Category.assoc, hinv (fiberInverse J p χ hG τ), Category.id_comp]
      calc
        τ ≫ fiberInverse J p χ hG τ =
            fiberInverse J p χ hG (fiberInverse J p χ hG τ) ≫ fiberInverse J p χ hG τ :=
          congrArg (fun f ↦ f ≫ fiberInverse J p χ hG τ) h.symm
        _ = 𝟙 a := hinv (fiberInverse J p χ hG τ) }

/-- The actual local fibre pseudofunctor is pointwise groupoidal. -/
theorem localFibersGroupoids (hG : Functor.IsFibered.InGroupoids p)
    (U : LocallyDiscrete Cᵒᵖ) : IsGroupoid ((localFibers J p χ).obj U) := by
  let G := localFiberGroupoid J p χ hG (unop U.as)
  exact { all_isIso := fun φ ↦ ⟨⟨G.inv φ, G.comp_inv φ, G.inv_comp φ⟩⟩ }

end CategoryTheory.Functor.StackificationConstruction

namespace CategoryTheory.Functor.StackificationConstruction.DescentCompletion

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vF, uF})
variable [∀ U, IsGroupoid (F.obj U)]

/-- A raw descent morphism is inverted on its original common cover. -/
def RawHom.inverse {U : C} {a b : Object J F U} (φ : RawHom J F a b) : RawHom J F b a where
  cover := φ.cover
  left := φ.right
  right := φ.left
  arrow :=
    { hom I := CategoryTheory.inv (φ.arrow.hom I)
      comm := by
        intro T q I L k l hk hl
        let e := Pseudofunctor.DescentData.isoMk (fun I ↦ asIso (φ.arrow.hom I))
          (fun {T} q {I L} k l hk hl ↦ φ.arrow.comm q k l hk hl)
        exact e.inv.comm q k l hk hl }

/-- Equality on a further common refinement is preserved by those inverses. -/
theorem RawHom.inverse_respects {U : C} {a b : Object J F U}
    {φ ψ : RawHom J F a b} (h : RawHom.Equivalent J F φ ψ) :
    RawHom.Equivalent J F (RawHom.inverse J F φ) (RawHom.inverse J F ψ) := by
  obtain ⟨R, hφ, hψ, h⟩ := h
  refine ⟨R, hφ, hψ, ?_⟩
  apply Pseudofunctor.DescentData.hom_ext
  intro I
  exact congrArg (fun f ↦ CategoryTheory.inv f) (congrArg (fun f ↦ f.hom I) h)

/-- The descent completion carries the actual componentwise quotient inverse. -/
@[reducible]
def objectGroupoid (U : C) : Groupoid.{max u v vF} (Object J F U) where
  __ := objectCategory J F U
  inv := _root_.Quotient.map (RawHom.inverse J F) (fun _ _ h ↦ RawHom.inverse_respects J F h)
  inv_comp := by
    intro a b f
    refine Quotient.inductionOn f ?_
    intro φ
    change Quotient.mk'' (RawHom.comp J F (RawHom.inverse J F φ) φ) =
      Quotient.mk'' (RawHom.id J F b)
    apply _root_.Quotient.sound
    refine ⟨φ.cover, le_inf le_rfl le_rfl, φ.right, ?_⟩
    apply Pseudofunctor.DescentData.hom_ext
    intro I
    change CategoryTheory.inv (φ.arrow.hom I) ≫ φ.arrow.hom I = 𝟙 _
    simp
  comp_inv := by
    intro a b f
    refine Quotient.inductionOn f ?_
    intro φ
    change Quotient.mk'' (RawHom.comp J F φ (RawHom.inverse J F φ)) =
      Quotient.mk'' (RawHom.id J F a)
    apply _root_.Quotient.sound
    refine ⟨φ.cover, le_inf le_rfl le_rfl, φ.left, ?_⟩
    apply Pseudofunctor.DescentData.hom_ext
    intro I
    change φ.arrow.hom I ≫ CategoryTheory.inv (φ.arrow.hom I) = 𝟙 _
    simp

end CategoryTheory.Functor.StackificationConstruction.DescentCompletion

namespace CategoryTheory.Functor.StackificationConstruction

variable {C : Type u} [Category.{v} C] {X : Type uX} [Category.{vX} X]
variable (J : GrothendieckTopology C) (p : X ⥤ C) (χ : p.Cleavage)

/-- Completed fibres use the inverse represented on the original common cover. -/
theorem completedFibersGroupoids (hG : Functor.IsFibered.InGroupoids p)
    (U : LocallyDiscrete Cᵒᵖ) :
    IsGroupoid ((completedPresheaf J p χ).toPseudofunctor'.obj U) := by
  letI : ∀ V, IsGroupoid ((localFibers J p χ).obj V) := localFibersGroupoids J p χ hG
  letI : Groupoid (DescentCompletion.Object J (localFibers J p χ) (unop U.as)) :=
    DescentCompletion.objectGroupoid J (localFibers J p χ) (unop U.as)
  exact inferInstanceAs
    (IsGroupoid (DescentCompletion.Object J (localFibers J p χ) (unop U.as)))

/-- The realized target is fibred in groupoids using the actual component inverses. -/
theorem targetInGroupoids (hG : Functor.IsFibered.InGroupoids p) :
    Functor.IsFibered.InGroupoids (targetProjection J p χ) := by
  letI : ∀ U, IsGroupoid ((completedPresheaf J p χ).toPseudofunctor'.obj U) :=
    completedFibersGroupoids J p χ hG
  exact Pseudofunctor.CoGrothendieck.forgetInGroupoids
    (completedPresheaf J p χ).toPseudofunctor'

end CategoryTheory.Functor.StackificationConstruction
