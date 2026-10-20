/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.NaiveCotangent.Presentation.Map

/-!
# Functoriality of canonical naive cotangent complexes

A commutative square of commutative-ring sheaves induces a canonical morphism between the
polynomial presentations and hence a morphism of naive cotangent complexes after extension of
scalars.  This file packages that frequently used specialization of the presentationwise API.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Sheaf

noncomputable section

universe c v w

namespace SheafOfModules.RingedSite.NaiveCotangent

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{w})]
variable [HasWeakSheafify J CommRingCat.{w}]
variable [HasSheafify J AddCommGrpCat.{w}]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {A B A' B' : Sheaf J CommRingCat.{w}}

/-- The map `A[B] ⟶ A'[B']` between canonical polynomial presentations induced by maps
`A ⟶ A'` and `B ⟶ B'`. -/
noncomputable def canonicalMiddle
    (α : A ⟶ B) (ρ : A ⟶ A') (β : A' ⟶ B') (φ : B ⟶ B') :
    FreeAlgebra.Presentation.underlying A (Under.mk α) ⟶
      FreeAlgebra.Presentation.underlying A' (Under.mk β) :=
  (FreeAlgebra.evaluation
    (Under.mk (ρ ≫ FreeAlgebra.Presentation.base A' (Under.mk β)))
    (FreeAlgebra.Presentation.generators (Under.mk α))
    ((sheafForget J).map φ ≫ FreeAlgebra.Presentation.generator A' (Under.mk β))).right

/-- The coefficient square for the canonical map between polynomial presentations commutes. -/
theorem canonicalMiddle_baseSq
    (α : A ⟶ B) (ρ : A ⟶ A') (β : A' ⟶ B') (φ : B ⟶ B') :
    CommSq ρ (FreeAlgebra.Presentation.base A (Under.mk α))
      (FreeAlgebra.Presentation.base A' (Under.mk β))
      (canonicalMiddle α ρ β φ) := sorry

/-- Commutativity of the original ring square makes the evaluation square for the canonical
map between polynomial presentations commute. -/
theorem canonicalMiddle_targetSq
    (α : A ⟶ B) (ρ : A ⟶ A') (β : A' ⟶ B') (φ : B ⟶ B')
    (sq : CommSq ρ α β φ) :
    CommSq (canonicalMiddle α ρ β φ) (FreeAlgebra.Presentation.map A (Under.mk α))
      (FreeAlgebra.Presentation.map A' (Under.mk β)) φ := sorry

/-- Equation 18.35.1.1: the morphism between canonical polynomial presentations induced by a
commutative square of ring sheaves. -/
@[stacks 08TX "morphism of canonical presentations"]
noncomputable def canonicalPresentationHom
    {α : A ⟶ B} {ρ : A ⟶ A'} {β : A' ⟶ B'} {φ : B ⟶ B'}
    (sq : CommSq ρ α β φ) :
    Presentation.Hom (FreeAlgebra.Presentation.base A (Under.mk α))
      (FreeAlgebra.Presentation.map A (Under.mk α))
      (FreeAlgebra.Presentation.base A' (Under.mk β))
      (FreeAlgebra.Presentation.map A' (Under.mk β)) where
  base := ρ
  middle := canonicalMiddle α ρ β φ
  target := φ
  baseSq := canonicalMiddle_baseSq α ρ β φ
  targetSq := canonicalMiddle_targetSq α ρ β φ sq

/-- Equation 18.35.1.1: the canonical map of naive cotangent complexes induced by a
commutative square, expressed in the extension-of-scalars form. -/
@[stacks 08TX]
noncomputable def map
    {α : A ⟶ B} {ρ : A ⟶ A'} {β : A' ⟶ B'} {φ : B ⟶ B'}
    (sq : CommSq ρ α β φ) :
    (extendComplex φ).obj (obj A (Under.mk α)) ⟶ obj A' (Under.mk β) :=
  Presentation.Hom.map (canonicalPresentationHom sq)

/-- The identity square on a morphism of commutative ring sheaves. -/
@[stacks 08TX "identity square for naive cotangent maps"]
theorem idSquare (α : A ⟶ B) : CommSq (𝟙 A) α α (𝟙 B) := sorry

/-- The canonical naive-cotangent map associated to the identity square is the
identity-extension comparison. -/
@[simp, stacks 08TX "identity law for naive cotangent maps"]
theorem map_id (α : A ⟶ B) :
    map (idSquare α) =
      (extendComplexIdIso B).hom.app (obj A (Under.mk α)) := sorry

/-- Canonical maps of naive cotangent complexes preserve composition of commutative squares,
with the standard comparison for successive extensions of scalars. -/
theorem map_comp
    {A'' B'' : Sheaf J CommRingCat.{w}}
    {α : A ⟶ B} {ρ : A ⟶ A'} {β : A' ⟶ B'} {φ : B ⟶ B'}
    {ρ' : A' ⟶ A''} {γ : A'' ⟶ B''} {φ' : B' ⟶ B''}
    (sq : CommSq ρ α β φ) (sq' : CommSq ρ' β γ φ') :
    map (CommSq.horiz_comp sq sq') =
      (extendComplexCompIso φ φ').inv.app (obj A (Under.mk α)) ≫
        (extendComplex φ').map (map sq) ≫ map sq' := sorry

end SheafOfModules.RingedSite.NaiveCotangent

-- The polynomial-algebra map is explicit; proof debt in the packaged presentation and complex
-- maps is confined to commutative-square and cochain-map law fields.
