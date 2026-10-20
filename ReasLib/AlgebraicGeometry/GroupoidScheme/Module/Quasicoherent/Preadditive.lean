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
  let zero : Zero (Hom A B) := ⟨of 0 sorry⟩
  let add : Add (Hom A B) := ⟨fun f g ↦ of (f.hom + g.hom) sorry⟩
  let neg : Neg (Hom A B) := ⟨fun f ↦ of (-f.hom) sorry⟩
  let sub : Sub (Hom A B) := ⟨fun f g ↦ of (f.hom - g.hom) sorry⟩
  let nsmul : SMul ℕ (Hom A B) := ⟨fun n f ↦ of (n • f.hom) sorry⟩
  let zsmul : SMul ℤ (Hom A B) := ⟨fun n f ↦ of (n • f.hom) sorry⟩
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
  add_comp := sorry
  comp_add := sorry

end AlgebraicGeometry.GroupoidScheme.QCoh
