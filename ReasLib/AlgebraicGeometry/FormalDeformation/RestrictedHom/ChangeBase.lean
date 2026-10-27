/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Elements
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Basic
public import ReasLib.AlgebraicGeometry.FormalDeformation.Prorepresentable
public import ReasLib.AlgebraicGeometry.FormalDeformation.RestrictedHom.Inverse
public import ReasLib.AlgebraicGeometry.FormalDeformation.TypesCompletion

/-!
# Changing-base 2-cell of explicit restricted Yoneda maps

A morphism `a : ξ ⟶ η` of formal objects, with base map `f = a.base`, induces a
based functor `underline S |_{C_Λ} ⥤ᵇ underline R |_{C_Λ}` by restricted coyoneda
precomposition, and a based 2-cell `underline ξ ∘ f ⟶ underline η` whose component
at `α : S ⟶ A` is the unique cofibered comparison `β_{m,*} ξ_m ⟶ α_{m,*} η_m`
over `id A`. Truncation index `n` denotes the quotient by the maximal-ideal power
`n + 1`, so the least vanishing positive exponent corresponds to the Lean stage
`nilpotencyIndex A`.
-/

@[expose] public section

open CategoryTheory IsLocalRing Opposite ArtinianLocalAlgCat CompleteLocalAlgCat
open scoped BasedFunctor

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CompleteLocalAlgCat

noncomputable section

/-- The based functor `underline S |_{C_Λ} ⥤ᵇ underline R |_{C_Λ}` induced by
precomposition with `f : R ⟶ S`. -/
def restrictedCoyonedaBasedMap {R S : CompleteLocalAlgCat Λ k} (f : R ⟶ S) :
    BasedCategory.ofFunctor (CategoryOfElements.π (restrictedCoyoneda S)) ⥤ᵇ
      BasedCategory.ofFunctor (CategoryOfElements.π (restrictedCoyoneda R)) :=
  BasedFunctor.ofFunctor (CategoryOfElements.map (restrictedCoyonedaMap f))
    (CategoryOfElements.map_π (restrictedCoyonedaMap f))

/-- The underlying functor of `restrictedCoyonedaBasedMap f` is the category-of-elements
map of `restrictedCoyonedaMap f`. -/
theorem restrictedCoyonedaBasedMap_toFunctor {R S : CompleteLocalAlgCat Λ k} (f : R ⟶ S) :
    (restrictedCoyonedaBasedMap f).toFunctor =
      CategoryOfElements.map (restrictedCoyonedaMap f) := sorry

/-- On objects, `restrictedCoyonedaBasedMap f` preserves the Artinian base and
precomposes the test map with `f`. -/
theorem restrictedCoyonedaBasedMap_obj {R S : CompleteLocalAlgCat Λ k} (f : R ⟶ S)
    (x : (restrictedCoyoneda S).Elements) :
    ((restrictedCoyonedaBasedMap f).obj x).1 = x.1 ∧
      ((restrictedCoyonedaBasedMap f).obj x).2 = f ≫ x.2 := sorry

end

end CompleteLocalAlgCat

variable {F : Type v} [Category.{v} F]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k}
variable [hp : Functor.IsFibered.InGroupoids p.op]

namespace FormalObject

noncomputable section

/-- Factoring `α ∘ f` through the truncation of `R` at the nilpotency index of `A`
is the induced truncation map followed by the corresponding factor of `α`. -/
theorem truncationFactor_comp {R S : CompleteLocalAlgCat Λ k}
    {A : ArtinianLocalAlgCat Λ k} (f : R ⟶ S) (α : S ⟶ inclusion.obj A) :
    truncationFactor (f ≫ α) =
      truncationHom f (nilpotencyIndex A) ≫ truncationFactor α := sorry

/-- Component at a test object `α : S ⟶ A` of the 2-cell `underline ξ ∘ f ⟶ underline η`:
the unique cofibered comparison `β_{m,*} ξ_m ⟶ α_{m,*} η_m` over `id A`. -/
def toRestrictedHom₂HomApp {ξ η : FormalObject p} (a : ξ ⟶ η)
    (x : (restrictedCoyoneda η.base).Elements) :
    toRestrictedHomObj ⟨ξ, rfl⟩
        ((CategoryOfElements.map (restrictedCoyonedaMap a.base)).obj x) ⟶
      toRestrictedHomObj ⟨η, rfl⟩ x :=
  let x' := (CategoryOfElements.map (restrictedCoyonedaMap a.base)).obj x
  let m := nilpotencyIndex x.1
  let fst := Quiver.Hom.op (truncationFactor x'.2)
  let ha := congrArg Opposite.op (stageOverFiber ⟨ξ, rfl⟩ m)
  let φ := Functor.IsPreFibered.pullbackMap (p := p.op)
      (a := Opposite.op (ξ.system.family m)) (ha := ha) fst
  let hφCart : p.op.IsCartesian fst φ :=
    Functor.IsPreFibered.pullbackMap.IsCartesian (p := p.op) ha fst
  let g := Quiver.Hom.op (𝟙 x.1)
  Along.stronglyCartesianUnop (p := p) fst φ g (g ≫ fst) rfl
    (Quiver.Hom.op (a.app m ≫ toRestrictedHomPush ⟨η, rfl⟩ x))
    (@Functor.IsFibered.isStronglyCartesian_of_isCartesian
      (ArtinianLocalAlgCat Λ k)ᵒᵖ Fᵒᵖ inferInstance inferInstance p.op inferInstance
      _ _ fst _ _ φ hφCart) (by
        letI : p.IsHomLift (a.baseTrunc m) (a.app m) := a.over m
        letI : p.IsHomLift (truncationFactor x.2) (toRestrictedHomPush ⟨η, rfl⟩ x) :=
          toRestrictedHomPush_isHomLift ⟨η, rfl⟩ x
        have h : p.IsHomLift (truncationFactor x'.2)
            (a.app m ≫ toRestrictedHomPush ⟨η, rfl⟩ x) := by
          change p.IsHomLift (truncationFactor (a.base ≫ x.2)) _
          with_unfolding_all
            rw [← truncationFactor_baseTrunc a x.2]
            infer_instance
        exact (Category.id_comp fst).symm ▸ Along.isHomLift_op h)

/-- The component `toRestrictedHom₂HomApp a x` lies over `id A`. -/
theorem toRestrictedHom₂HomApp_over {ξ η : FormalObject p} (a : ξ ⟶ η)
    (x : (restrictedCoyoneda η.base).Elements) :
    p.IsHomLift (𝟙 x.1) (toRestrictedHom₂HomApp a x) := sorry

/-- The cofibered comparison square: the pushforward of `ξ_m` along `β_m`, followed by
the component, equals `a_m` followed by the pushforward of `η_m` along `α_m`. -/
theorem toRestrictedHom₂HomApp_comm {ξ η : FormalObject p} (a : ξ ⟶ η)
    (x : (restrictedCoyoneda η.base).Elements) :
    toRestrictedHomPush ⟨ξ, rfl⟩
          ((CategoryOfElements.map (restrictedCoyonedaMap a.base)).obj x) ≫
        toRestrictedHom₂HomApp a x =
      a.app (nilpotencyIndex x.1) ≫ toRestrictedHomPush ⟨η, rfl⟩ x := sorry

/-- The based 2-cell `underline ξ ∘ f ⟶ underline η` over `C_Λ` induced by a morphism
of formal objects. -/
def toRestrictedHom₂Hom {ξ η : FormalObject p} (a : ξ ⟶ η) :
    restrictedCoyonedaBasedMap a.base ⋙ (toRestrictedHom ξ.base).obj ⟨ξ, rfl⟩ ⟶
      (toRestrictedHom η.base).obj ⟨η, rfl⟩ where
  toNatTrans :=
    { app := fun x ↦ toRestrictedHom₂HomApp a x
      naturality := sorry }
  isHomLift' := fun x => toRestrictedHom₂HomApp_over a x

/-- The component of `toRestrictedHom₂Hom a` at a test object is `toRestrictedHom₂HomApp`. -/
theorem toRestrictedHom₂Hom_app {ξ η : FormalObject p} (a : ξ ⟶ η)
    (x : (restrictedCoyoneda η.base).Elements) :
    (toRestrictedHom₂Hom a).toNatTrans.app x = toRestrictedHom₂HomApp a x := sorry

end

end FormalObject
