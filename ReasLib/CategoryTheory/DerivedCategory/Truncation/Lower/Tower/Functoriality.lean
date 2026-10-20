/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Truncation.Lower.Tower
public import ReasLib.CategoryTheory.Triangulated.TStructure.TruncGE.Sequence.Functoriality

@[expose] public section

/-!
# Functoriality of the Lower Derived-Truncation Tower

The canonical tower `n ↦ τ≥(-n) K` is functorial in the derived object. This
leaf specializes the generic antitone truncation-sequence API.
-/

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Triangulated.TStructure.TruncGE
open DerivedCategory.TStructure

universe w v u

namespace CategoryTheory.DerivedCategory.Truncation.Lower

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

/-- Stacks 0H72: a morphism of derived objects induces the componentwise
canonical morphism of their lower-truncation towers. -/
@[stacks 0H72]
noncomputable def towerMap {K L : DerivedCategory 𝒜} (f : K ⟶ L) :
    tower K ⟶ tower L :=
  Sequence.map t f index
    (fun _ _ h ↦ neg_le_neg (Int.ofNat_le_ofNat_of_le h))

/-- A component of `towerMap f` is the corresponding lower-truncation map. -/
@[simp, stacks 0H72]
theorem towerMap_app {K L : DerivedCategory 𝒜} (f : K ⟶ L) (n : ℕ) :
    (towerMap f).app (op n) = (t.truncGE (index n)).map f := sorry

/-- The lower-tower map induced by an identity is the identity. -/
@[simp, stacks 0H72]
theorem towerMap_id (K : DerivedCategory 𝒜) :
    towerMap (𝟙 K) = 𝟙 (tower K) := sorry

/-- Lower-tower maps preserve composition. -/
@[simp, stacks 0H72]
theorem towerMap_comp {K L M : DerivedCategory 𝒜} (f : K ⟶ L) (g : L ⟶ M) :
    towerMap (f ≫ g) = towerMap f ≫ towerMap g := sorry

variable (𝒜) in
/-- Stacks 0H72: taking the canonical lower-truncation tower is functorial
in the derived object. -/
@[stacks 0H72]
noncomputable def towerFunctor :
    DerivedCategory 𝒜 ⥤ SequentialInverseSystem (DerivedCategory 𝒜) :=
  Sequence.functor t index
    (fun _ _ h ↦ neg_le_neg (Int.ofNat_le_ofNat_of_le h))

/-- Evaluating `towerFunctor` gives the canonical lower-truncation tower. -/
@[simp, stacks 0H72]
theorem towerFunctor_obj (K : DerivedCategory 𝒜) :
    (towerFunctor 𝒜).obj K = tower K := sorry

/-- The map of `towerFunctor` is the canonical componentwise tower map. -/
@[simp, stacks 0H72]
theorem towerFunctor_map {K L : DerivedCategory 𝒜} (f : K ⟶ L) :
    (towerFunctor 𝒜).map f = towerMap f := sorry

/-- A lower-tower map commutes with every transition map. -/
@[reassoc, stacks 0H72]
theorem transitionMap_comp_towerMap_app {K L : DerivedCategory 𝒜}
    (f : K ⟶ L) {m n : ℕ} (h : m ≤ n) :
    (tower K).transitionMap h ≫ (towerMap f).app (op m) =
      (towerMap f).app (op n) ≫ (tower L).transitionMap h := sorry

end CategoryTheory.DerivedCategory.Truncation.Lower
