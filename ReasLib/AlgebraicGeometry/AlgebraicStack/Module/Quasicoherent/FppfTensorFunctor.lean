/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.Quasicoherent.FppfTensor
public import Mathlib.CategoryTheory.Products.Basic

/-! # Functoriality of the direct fppf quasi-coherent tensor product -/

@[expose] public section

open AlgebraicGeometry CategoryTheory AlgebraicGeometry.GroupoidsOver
  SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.QCoh.Fppf

variable {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]

/-- The tensor product of morphisms of quasi-coherent modules, transported
from the commutative fppf coefficient presentation. -/
def tensorMap {A A' B B' : QCoh X} (f : A ⟶ A') (g : B ⟶ B') :
    tensor A B ⟶ tensor A' B' :=
  ObjectProperty.homMk
    ((fromCommFppfModules X).map
      (@moduleTensorMap.{u + 1, u, u}
        X.total inferInstance (X.associatedTopology .fppf)
        (associatedTopology_hasSheafCompose_commRing X .fppf)
        (associatedTopology_hasWeakSheafify X .fppf)
        (associatedTopology_wEqualsLocallyBijective X .fppf)
        (commAssociatedStructureSheaf X .fppf) _ _ _ _
        ((toCommFppfModules X).map f.hom)
        ((toCommFppfModules X).map g.hom)))

/-- Tensor products of quasi-coherent morphisms preserve identities and
simultaneous composition in both variables. -/
theorem tensorMap_laws :
    (∀ A B : QCoh X, tensorMap (𝟙 A) (𝟙 B) = 𝟙 (tensor A B)) ∧
      (∀ {A A' A'' B B' B'' : QCoh X}
        (f : A ⟶ A') (f' : A' ⟶ A'') (g : B ⟶ B') (g' : B' ⟶ B''),
        tensorMap (f ≫ f') (g ≫ g') = tensorMap f g ≫ tensorMap f' g') :=
  sorry

/-- Tensor product as a bifunctor on quasi-coherent modules in the direct
fppf coefficient presentation. -/
def tensorBifunctor (X : GroupoidsOver S) [AlgebraicStack X] :
    QCoh X × QCoh X ⥤ QCoh X where
  obj A := tensor A.1 A.2
  map f := tensorMap f.1 f.2
  map_id A := tensorMap_laws.1 A.1 A.2
  map_comp f g := tensorMap_laws.2 f.1 g.1 f.2 g.2

end AlgebraicGeometry.GroupoidsOver.QCoh.Fppf
