/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.Coherent.Category
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.Quasicoherent.FppfTensorFunctor

/-! # Tensor products of coherent modules and their quasi-coherent inclusion -/

@[expose] public section

open AlgebraicGeometry CategoryTheory AlgebraicGeometry.GroupoidsOver

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.Coh

variable {S : Scheme.{u}} {X : GroupoidsOver S}
variable [AlgebraicStack X] [IsLocallyNoetherian X]

/-- The quasi-coherent tensor product of two coherent modules on a locally
Noetherian algebraic stack has coherent underlying module. -/
theorem tensor_isCoherent (A B : Coh X) :
    AlgebraicStack.IsCoherent
      (QCoh.Fppf.tensor (toQCoh.obj A) (toQCoh.obj B)).obj :=
  sorry

/-- Tensor product of coherent modules, computed as the quasi-coherent tensor
product of their inclusions. -/
def tensor (A B : Coh X) : Coh X where
  obj := (QCoh.Fppf.tensor (toQCoh.obj A) (toQCoh.obj B)).obj
  property := tensor_isCoherent A B

/-- The underlying module of the coherent tensor product is the underlying
module of the quasi-coherent tensor product. -/
theorem tensor_obj (A B : Coh X) :
    (tensor A B).obj = (QCoh.Fppf.tensor (toQCoh.obj A) (toQCoh.obj B)).obj :=
  rfl

/-- Tensor product of morphisms of coherent modules, computed on their
underlying quasi-coherent modules. -/
def tensorMap {A A' B B' : Coh X} (f : A ⟶ A') (g : B ⟶ B') :
    tensor A B ⟶ tensor A' B' :=
  ObjectProperty.homMk
    (QCoh.Fppf.tensorMap (toQCoh.map f) (toQCoh.map g)).hom

/-- Tensor products of coherent morphisms preserve identities and simultaneous
composition in both variables. -/
theorem tensorMap_laws :
    (∀ A B : Coh X, tensorMap (𝟙 A) (𝟙 B) = 𝟙 (tensor A B)) ∧
      (∀ {A A' A'' B B' B'' : Coh X}
        (f : A ⟶ A') (f' : A' ⟶ A'') (g : B ⟶ B') (g' : B' ⟶ B''),
        tensorMap (f ≫ f') (g ≫ g') = tensorMap f g ≫ tensorMap f' g') :=
  sorry

/-- Tensor product as a bifunctor on coherent modules on a locally Noetherian
algebraic stack. -/
def tensorBifunctor (X : GroupoidsOver S) [AlgebraicStack X]
    [IsLocallyNoetherian X] : Coh X × Coh X ⥤ Coh X where
  obj A := tensor A.1 A.2
  map f := tensorMap f.1 f.2
  map_id A := tensorMap_laws.1 A.1 A.2
  map_comp f g := tensorMap_laws.2 f.1 g.1 f.2 g.2

/-- Inclusion into quasi-coherent modules identifies the coherent tensor with
the quasi-coherent tensor of the included modules. -/
def tensor_toQCohIso (A B : Coh X) :
    toQCoh.obj (tensor A B) ≅ QCoh.Fppf.tensor (toQCoh.obj A) (toQCoh.obj B) :=
  ObjectProperty.isoMk (quasiCoherentModuleProperty X) (Iso.refl _)

/-- The canonical comparison between coherent and quasi-coherent tensor
products is natural in both coherent modules. -/
theorem tensor_toQCohIso_naturality {A A' B B' : Coh X}
    (f : A ⟶ A') (g : B ⟶ B') :
    toQCoh.map (tensorMap f g) ≫ (tensor_toQCohIso A' B').hom =
      (tensor_toQCohIso A B).hom ≫ QCoh.Fppf.tensorMap (toQCoh.map f) (toQCoh.map g) :=
  sorry

/-- The inclusion of coherent modules into quasi-coherent modules commutes
naturally with the tensor bifunctors. -/
def tensorBifunctor_toQCohIso :
    tensorBifunctor X ⋙ toQCoh ≅
      Functor.prod (toQCoh : Coh X ⥤ QCoh X) toQCoh ⋙ QCoh.Fppf.tensorBifunctor X :=
  NatIso.ofComponents (fun A ↦ tensor_toQCohIso A.1 A.2)
    (fun f ↦ tensor_toQCohIso_naturality f.1 f.2)

end AlgebraicGeometry.AlgebraicStack.Coh
