/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Module.Quasicoherent

/-!
# Preadditive structure on equivariant quasi-coherent modules

Equivariant morphisms inherit pointwise addition from their underlying
quasi-coherent-module morphisms, making equivariant quasi-coherent modules a
preadditive category.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme.System.Hom

/-- Equivariant morphisms form an additive commutative group under the pointwise
operations on their underlying quasi-coherent-module morphisms. -/
@[reducible]
def addCommGroup {S : Scheme.{u}} {G : GroupoidScheme S} (A B : System G) :
    AddCommGroup (Hom A B) :=
  let pullback_additive {X Y : Scheme.{u}} (f : X ⟶ Y) :
      (Scheme.QCoh.pullback f).Additive := by
    constructor
    intro F H a b
    apply ObjectProperty.hom_ext
    change (Scheme.Modules.pullback f).map (a.hom + b.hom) =
      (Scheme.Modules.pullback f).map a.hom + (Scheme.Modules.pullback f).map b.hom
    exact Functor.map_add _
  letI := pullback_additive G.t.left
  letI := pullback_additive G.s.left
  let zero : Zero (Hom A B) := ⟨of 0 (by simp)⟩
  let add : Add (Hom A B) := ⟨fun f g ↦ of (f.hom + g.hom) (by
    simp only [Functor.map_add, Preadditive.add_comp, Preadditive.comp_add,
      f.compatibility, g.compatibility])⟩
  let neg : Neg (Hom A B) := ⟨fun f ↦ of (-f.hom) (by
    simp only [Functor.map_neg, Preadditive.neg_comp, Preadditive.comp_neg,
      f.compatibility])⟩
  let sub : Sub (Hom A B) := ⟨fun f g ↦ of (f.hom - g.hom) (by
    simp only [Functor.map_sub, Preadditive.sub_comp, Preadditive.comp_sub,
      f.compatibility, g.compatibility])⟩
  let nsmul : SMul ℕ (Hom A B) := ⟨fun n f ↦ of (n • f.hom) (by
    simpa only [Functor.map_nsmul, Preadditive.nsmul_comp, Preadditive.comp_nsmul]
      using congrArg (fun h ↦ n • h) f.compatibility)⟩
  let zsmul : SMul ℤ (Hom A B) := ⟨fun n f ↦ of (n • f.hom) (by
    simpa only [Functor.map_zsmul, Preadditive.zsmul_comp, Preadditive.comp_zsmul]
      using congrArg (fun h ↦ n • h) f.compatibility)⟩
  @Function.Injective.addCommGroup (Hom A B) (A.obj ⟶ B.obj)
    add zero nsmul neg sub zsmul inferInstance (fun f ↦ f.hom)
      (fun _ _ h ↦ ext h) rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl)
        (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

end AlgebraicGeometry.GroupoidScheme.System.Hom

namespace AlgebraicGeometry.GroupoidScheme.QCoh

/-- Equivariant quasi-coherent modules form a preadditive category. -/
@[reducible]
def preadditive {S : Scheme.{u}} (G : GroupoidScheme S) : Preadditive G.QCoh where
  homGroup A B := System.Hom.addCommGroup A B
  add_comp A B C f g h := by
    apply System.Hom.ext
    change (f.hom + g.hom) ≫ h.hom = f.hom ≫ h.hom + g.hom ≫ h.hom
    exact Preadditive.add_comp _ _ _ _ _ _
  comp_add A B C f g h := by
    apply System.Hom.ext
    change f.hom ≫ (g.hom + h.hom) = f.hom ≫ g.hom + f.hom ≫ h.hom
    exact Preadditive.comp_add _ _ _ _ _ _

end AlgebraicGeometry.GroupoidScheme.QCoh
