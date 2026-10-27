/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Lifts
public import Mathlib.CategoryTheory.FiberedCategory.Fiber

/-!
# Transport of lifts along composable base morphisms
-/

@[expose] public section

open CategoryTheory

universe v₁ u₁ v₂ u₂

namespace CategoryTheory.Functor

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₂} 𝒳]
variable {p : 𝒳 ⥤ 𝒮}

namespace ObjectLift

/-- Reindex a lift along an equality of base morphisms. -/
def congr {R S : 𝒮} {f g : R ⟶ S} (h : f = g) {x : p.Fiber S}
    (a : ObjectLift p f x) : ObjectLift p g x :=
  ⟨a.val, h ▸ a.property⟩

/-- Reindexing a lift does not change its underlying total morphism. -/
theorem congr_hom {R S : 𝒮} {f g : R ⟶ S} (h : f = g) {x : p.Fiber S}
    (a : ObjectLift p f x) :
    (congr h a).hom = a.hom := by
  rfl

/-- Push a lift along the first morphism of a composite using the opposite-cartesian
factorization supplied by fibredness. -/
noncomputable def pushforwardAlong [IsFibered.InGroupoids p.op]
    {R S T : 𝒮} (u : R ⟶ S) (f : S ⟶ T) {x : p.Fiber T}
    (a : ObjectLift p (u ≫ f) x) : ObjectLift p f x := by
  let u' : p.obj a.left ⟶ S :=
    eqToHom (IsHomLift.domain_eq p (u ≫ f) a.hom) ≫ u
  let φ := IsPreFibered.pullbackMap (p := p.op)
    (a := Opposite.op a.left)
    (rfl : p.op.obj (Opposite.op a.left) = Opposite.op (p.obj a.left))
    (Quiver.Hom.op u' : Opposite.op S ⟶ Opposite.op (p.obj a.left))
  let hφ : p.op.IsCartesian
      (Quiver.Hom.op u' : Opposite.op S ⟶ Opposite.op (p.obj a.left)) φ :=
    IsPreFibered.pullbackMap.IsCartesian (p := p.op)
      (a := Opposite.op a.left)
      (rfl : p.op.obj (Opposite.op a.left) = Opposite.op (p.obj a.left))
      (Quiver.Hom.op u' : Opposite.op S ⟶ Opposite.op (p.obj a.left))
  let hφ' : p.op.IsStronglyCartesian
      (Quiver.Hom.op u' : Opposite.op S ⟶ Opposite.op (p.obj a.left)) φ :=
    IsFibered.isStronglyCartesian_of_isCartesian p.op
      (Quiver.Hom.op u' : Opposite.op S ⟶ Opposite.op (p.obj a.left)) φ
  have hlift : p.IsHomLift (u' ≫ f) a.hom := by
    simpa only [u', Category.assoc] using
      (inferInstance : p.IsHomLift
        (eqToHom (IsHomLift.domain_eq p (u ≫ f) a.hom) ≫ (u ≫ f)) a.hom)
  have op_lift {R S : 𝒮} {a b : 𝒳} (g : R ⟶ S) (φ : a ⟶ b)
      (h : p.IsHomLift g φ) : p.op.IsHomLift g.op φ.op := by
    cases h
    exact IsHomLift.map (p := p.op) _
  letI : p.op.IsHomLift (u' ≫ f).op a.hom.op := op_lift _ _ hlift
  letI : p.op.IsStronglyCartesian u'.op φ := hφ'
  let m := @IsStronglyCartesian.map _ _ _ _ p.op
      (Opposite.op S) (Opposite.op (p.obj a.left))
      (IsPreFibered.pullbackObj
        (p := p.op) (a := Opposite.op a.left)
        (rfl : p.op.obj (Opposite.op a.left) = Opposite.op (p.obj a.left))
        (Quiver.Hom.op u'))
      (Opposite.op a.left)
      (Quiver.Hom.op u') φ hφ'
      (Opposite.op T) (Opposite.op (Fiber.fiberInclusion.obj x))
      (Quiver.Hom.op f) (Quiver.Hom.op (u' ≫ f)) rfl
      (Quiver.Hom.op a.hom) inferInstance
  have unop_lift {R S : 𝒮ᵒᵖ} {a b : 𝒳ᵒᵖ} (g : R ⟶ S) (φ : a ⟶ b)
      (h : p.op.IsHomLift g φ) : p.IsHomLift g.unop φ.unop := by
    cases h
    exact IsHomLift.map (p := p) _
  exact ⟨Over.mk (Quiver.Hom.unop m), unop_lift f.op m (by dsimp [m]; infer_instance)⟩

/-- The transported lift lies over the second base morphism and has its expected
domain object. -/
theorem pushforwardAlong_spec [IsFibered.InGroupoids p.op]
    {R S T : 𝒮} (u : R ⟶ S) (f : S ⟶ T) {x : p.Fiber T}
    (a : ObjectLift p (u ≫ f) x) :
    p.IsHomLift f (pushforwardAlong u f a).hom ∧
      p.obj (pushforwardAlong u f a).left = S :=
  ⟨(pushforwardAlong u f a).property,
    IsHomLift.domain_eq p f (pushforwardAlong u f a).hom⟩

end ObjectLift

end CategoryTheory.Functor
