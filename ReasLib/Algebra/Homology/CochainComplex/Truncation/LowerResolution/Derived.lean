/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.CochainComplex.Truncation.LowerResolution.Functoriality
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyLimit.Comparison

@[expose] public section

/-!
# Derived Comparisons for Lower-Truncation Towers

This leaf sends the canonical lower-truncation tower of a cochain complex to
its derived category and specializes the generic `HomotopyLimit.Comparison`
bundle to that tower.  It does not choose a derived category instance or a
Milnor product presentation.
-/

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe w u v

namespace CochainComplex.LowerTruncation

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

/-- Stacks 070M: the canonical lower-truncation diagram after passage to the derived category.
-/
@[stacks 070M]
noncomputable def derivedTower (K : CochainComplex 𝒜 ℤ) :
    SequentialInverseSystem (DerivedCategory 𝒜) :=
  diagram K ⋙ DerivedCategory.Q

variable (𝒜) in
/-- The lower-truncation derived tower, functorial in the original cochain
complex.  It is obtained by postcomposing the ordinary truncation diagram
functor with the derived localization. -/
@[stacks 070M]
noncomputable def derivedTowerFunctor :
    CochainComplex 𝒜 ℤ ⥤ (ℕᵒᵖ ⥤ DerivedCategory 𝒜) :=
  diagramFunctor 𝒜 ⋙
    (Functor.whiskeringRight ℕᵒᵖ (CochainComplex 𝒜 ℤ)
      (DerivedCategory 𝒜)).obj DerivedCategory.Q

/-- On objects, `derivedTowerFunctor` is the canonical derived lower-
truncation tower. -/
@[simp, stacks 070M]
theorem derivedTowerFunctor_obj (K : CochainComplex 𝒜 ℤ) :
    (derivedTowerFunctor 𝒜).obj K = derivedTower K := by
  rfl

/-- A component of the functorial map between derived lower-truncation
towers is the localization of the corresponding truncation map. -/
@[simp, stacks 070M]
theorem derivedTowerFunctor_map_app {K L : CochainComplex 𝒜 ℤ}
    (f : K ⟶ L) (n : ℕ) :
    ((derivedTowerFunctor 𝒜).map f).app (op n) =
      DerivedCategory.Q.map (CochainComplex.truncGEMap f (index n)) := by
  rfl

/-- Stacks 070M: the canonical map from a complex to the `n`th derived lower-truncation stage.
-/
@[stacks 070M]
noncomputable abbrev derivedToStage (K : CochainComplex 𝒜 ℤ) (n : ℕ) :
    DerivedCategory.Q.obj K ⟶ (derivedTower K).obj (op n) :=
  DerivedCategory.Q.map (K.πTruncGE (index n))

/-- The canonical cone from a complex in the derived category to the derived
images of its lower truncations. -/
@[stacks 070M]
noncomputable def derivedSourceCone (K : CochainComplex 𝒜 ℤ) :
    Cone (derivedTower K) :=
  DerivedCategory.Q.mapCone (sourceCone K)

/-- The legs of `derivedSourceCone K` are the canonical derived maps to the
lower-truncation stages. -/
@[simp, stacks 070M]
theorem derivedSourceCone_π_app (K : CochainComplex 𝒜 ℤ) (n : ℕ) :
    (derivedSourceCone K).π.app (op n) = derivedToStage K n := by
  rfl

/-- The maps from a complex to its derived lower truncations are natural in
the original cochain complex. -/
@[reassoc, stacks 070M]
theorem derivedToStage_naturality {K L : CochainComplex 𝒜 ℤ}
    (f : K ⟶ L) (n : ℕ) :
    DerivedCategory.Q.map f ≫ derivedToStage L n =
      derivedToStage K n ≫ ((derivedTowerFunctor 𝒜).map f).app (op n) := by
  change DerivedCategory.Q.map f ≫ DerivedCategory.Q.map (L.πTruncGE (index n)) =
    DerivedCategory.Q.map (K.πTruncGE (index n)) ≫
      DerivedCategory.Q.map (CochainComplex.truncGEMap f (index n))
  rw [← Functor.map_comp, ← Functor.map_comp,
    CochainComplex.πTruncGE_naturality]

/-- The derived lower-truncation cone legs are natural in the original
cochain complex. -/
@[stacks 070M]
theorem derivedSourceNatTrans_naturality
    {K L : CochainComplex 𝒜 ℤ} (f : K ⟶ L) :
    (DerivedCategory.Q ⋙ Functor.const ℕᵒᵖ).map f ≫
        (derivedSourceCone L).π =
      (derivedSourceCone K).π ≫ (derivedTowerFunctor 𝒜).map f := by
  ext j
  exact derivedToStage_naturality f j.unop

variable (𝒜) in
/-- The canonical derived maps from a complex to all of its lower
truncations, natural in the original complex. -/
@[stacks 070M]
noncomputable def derivedSourceNatTrans :
    DerivedCategory.Q ⋙ Functor.const ℕᵒᵖ ⟶ derivedTowerFunctor 𝒜 where
  app K := (derivedSourceCone K).π
  naturality _ _ f := derivedSourceNatTrans_naturality f

/-- The component of `derivedSourceNatTrans` is the canonical derived
lower-truncation source-cone transformation. -/
@[simp, stacks 070M]
theorem derivedSourceNatTrans_app (K : CochainComplex 𝒜 ℤ) :
    (derivedSourceNatTrans 𝒜).app K = (derivedSourceCone K).π := by
  rfl

/-- Evaluating `derivedSourceNatTrans` at a truncation stage gives the
canonical derived map to that stage. -/
@[simp, stacks 070M]
theorem derivedSourceNatTrans_app_app
    (K : CochainComplex 𝒜 ℤ) (n : ℕ) :
    ((derivedSourceNatTrans 𝒜).app K).app (op n) =
      derivedToStage K n := by
  rfl

/-- A cochain map induces the canonical morphism between the corresponding
derived source cones after postcomposition along the map of derived towers. -/
@[stacks 070M]
noncomputable def derivedSourceConeMap {K L : CochainComplex 𝒜 ℤ}
    (f : K ⟶ L) :
    (Cone.postcompose ((derivedTowerFunctor 𝒜).map f)).obj (derivedSourceCone K) ⟶
      derivedSourceCone L where
  hom := DerivedCategory.Q.map f
  w j := derivedToStage_naturality f j.unop

/-- The apex map of `derivedSourceConeMap f` is the localization of `f`. -/
@[simp, stacks 070M]
theorem derivedSourceConeMap_hom {K L : CochainComplex 𝒜 ℤ}
    (f : K ⟶ L) :
    (derivedSourceConeMap f).hom = DerivedCategory.Q.map f := by
  rfl

/-- The canonical derived maps to lower truncations commute with the successor transition. -/
@[reassoc (attr := simp), stacks 070M]
theorem derivedToStage_comp_transition (K : CochainComplex 𝒜 ℤ) (n : ℕ) :
    derivedToStage K (n + 1) ≫ (derivedTower K).transitionMap (Nat.le_succ n) =
      derivedToStage K n := by
  change DerivedCategory.Q.map (K.πTruncGE (index (n + 1))) ≫
    DerivedCategory.Q.map ((diagram K).map (homOfLE (Nat.le_succ n)).op) =
      DerivedCategory.Q.map (K.πTruncGE (index n))
  rw [show (diagram K).map (homOfLE (Nat.le_succ n)).op = step K n from
    Functor.ofOpSequence_map_homOfLE_succ (step K) n, ← Functor.map_comp]
  apply congrArg DerivedCategory.Q.map
  change K.πTruncGE (index (n + 1)) ≫ step K n = K.πTruncGE (index n)
  letI : (K.truncGE (index n)).IsStrictlyGE (index (n + 1)) :=
    (K.truncGE (index n)).isStrictlyGE_of_ge (index (n + 1)) (index n)
      (neg_le_neg (Int.ofNat_le_ofNat_of_le (Nat.le_succ (n + 1))))
  dsimp only [step, truncGEMapOfLE]
  rw [← Category.assoc, CochainComplex.πTruncGE_naturality,
    Category.assoc, IsIso.hom_inv_id, Category.comp_id]

/-- Stacks 070M: concrete comparison data from `K` to a derived limit of its canonical
lower-truncation tower. -/
@[stacks 070M]
abbrev Comparison (K : CochainComplex 𝒜 ℤ) {L : DerivedCategory 𝒜}
    (c : DerivedCategory.Q.obj K ⟶ L) : Type _ :=
  HomotopyLimit.Comparison (derivedSourceCone K) c

/-- Stacks 070M: the proposition that a morphism is a compatible comparison to a derived limit
of the canonical lower-truncation tower. -/
@[stacks 070M]
def Comparison.Exists (K : CochainComplex 𝒜 ℤ) {L : DerivedCategory 𝒜}
    (c : DerivedCategory.Q.obj K ⟶ L) : Prop :=
  Nonempty (Comparison K c)

namespace Comparison.Exists

/-- Stacks 070M: two compatible comparisons from the same complex to derived limits of its
lower-truncation tower are simultaneously isomorphisms. -/
@[stacks 070M]
theorem isIso_iff {K : CochainComplex 𝒜 ℤ}
    {L L' : DerivedCategory 𝒜} {c : DerivedCategory.Q.obj K ⟶ L}
    {c' : DerivedCategory.Q.obj K ⟶ L'}
    (hc : Comparison.Exists K c) (hc' : Comparison.Exists K c') :
    IsIso c ↔ IsIso c' := sorry

end Comparison.Exists

end CochainComplex.LowerTruncation
