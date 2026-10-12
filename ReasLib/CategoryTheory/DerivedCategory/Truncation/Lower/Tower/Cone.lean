/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Truncation.Lower.Tower.Functoriality
public import ReasLib.CategoryTheory.Triangulated.TStructure.TruncGE.Sequence.Cone

@[expose] public section

/-!
# Canonical Cones over the Lower Derived-Truncation Tower

The canonical projections `K ⟶ τ≥(-n) K` assemble naturally into a morphism
of inverse systems and into a cone over the lower derived-truncation tower.
-/

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Triangulated.TStructure.TruncGE
open DerivedCategory.TStructure

universe w v u

namespace CategoryTheory.DerivedCategory.Truncation.Lower

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

/-- Stacks 0H72: the canonical morphism from the constant inverse system at
`K` to its lower derived-truncation tower. -/
@[stacks 0H72]
noncomputable def toTower (K : DerivedCategory 𝒜) :
    (Functor.const ℕᵒᵖ).obj K ⟶ tower K :=
  Sequence.πApp t K index
    (fun _ _ h ↦ neg_le_neg (Int.ofNat_le_ofNat_of_le h))

/-- A component of `toTower K` is the canonical map to that truncation stage. -/
@[simp, stacks 0H72]
theorem toTower_app (K : DerivedCategory 𝒜) (n : ℕ) :
    (toTower K).app (op n) = toStage K n := sorry

/-- Canonical maps to lower truncations commute with every transition map. -/
@[reassoc (attr := simp), stacks 0H72]
theorem toStage_comp_transitionMap (K : DerivedCategory 𝒜)
    {m n : ℕ} (h : m ≤ n) :
    toStage K n ≫ (tower K).transitionMap h = toStage K m := sorry

/-- The canonical morphisms to lower towers are natural in the derived object. -/
@[reassoc, stacks 0H72]
theorem toTower_naturality {K L : DerivedCategory 𝒜} (f : K ⟶ L) :
    (Functor.const ℕᵒᵖ).map f ≫ toTower L =
      toTower K ≫ towerMap f := sorry

variable (𝒜) in
/-- Stacks 0H72: the canonical maps to lower truncations, natural in the
derived object. -/
@[stacks 0H72]
noncomputable def toTowerNatTrans :
    Functor.const ℕᵒᵖ ⟶ towerFunctor 𝒜 :=
  Sequence.π t index
    (fun _ _ h ↦ neg_le_neg (Int.ofNat_le_ofNat_of_le h))

/-- Evaluating `toTowerNatTrans` gives the canonical morphism to the tower. -/
@[simp, stacks 0H72]
theorem toTowerNatTrans_app (K : DerivedCategory 𝒜) :
    (toTowerNatTrans 𝒜).app K = toTower K := sorry

/-- Stacks 0H72: the canonical cone from a derived object to its lower
derived-truncation tower. -/
@[stacks 0H72]
noncomputable def cone (K : DerivedCategory 𝒜) : Cone (tower K) :=
  Sequence.cone t K index
    (fun _ _ h ↦ neg_le_neg (Int.ofNat_le_ofNat_of_le h))

/-- The point of the canonical lower-truncation cone is the original object. -/
@[simp, stacks 0H72]
theorem cone_pt (K : DerivedCategory 𝒜) : (cone K).pt = K := sorry

/-- A leg of the canonical cone is the canonical map to that truncation stage. -/
@[simp, stacks 0H72]
theorem cone_π_app (K : DerivedCategory 𝒜) (n : ℕ) :
    (cone K).π.app (op n) = toStage K n := sorry

/-- A derived morphism induces the canonical morphism between its lower
truncation cones. -/
@[stacks 0H72]
noncomputable def coneMap {K L : DerivedCategory 𝒜} (f : K ⟶ L) :
    (Cone.postcompose (towerMap f)).obj (cone K) ⟶ cone L :=
  Sequence.coneMap t f index
    (fun _ _ h ↦ neg_le_neg (Int.ofNat_le_ofNat_of_le h))

/-- The apex map of the canonical lower-truncation cone morphism is the
original morphism. -/
@[simp, stacks 0H72]
theorem coneMap_hom {K L : DerivedCategory 𝒜} (f : K ⟶ L) :
    (coneMap f).hom = f := sorry

end CategoryTheory.DerivedCategory.Truncation.Lower
