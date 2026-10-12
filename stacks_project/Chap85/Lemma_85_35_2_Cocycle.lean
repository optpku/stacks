/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import ReasLib.CategoryTheory.DerivedCategory.Ext
public import stacks_project.Chap75.Definition_75_5_1_DerivedQCoh
public import stacks_project.Chap75.Lemma_75_20_4_BaseChange
public import stacks_project.Chap75.Lemma_75_26_4_Pullback
public import stacks_project.Chap85.Lemma_85_12_4_Descent

/-!
# Forward C₂ cocycles for derived pullbacks on simplicial algebraic spaces

An isomorphism `α : L(δ 1)^* K0 ≅ L(δ 0)^* K0` on `U_1` is a `C₂` cocycle when the
nine actual coface maps satisfy the forward test-object criterion. Vertex pullbacks
`K_n = Lf_{τ^n_n}^* K0`, recoded composition comparisons, compatibility of a
stage-zero isomorphism with `α`, and negative self-Ext vanishing are recorded here
for later glueing.
-/

@[expose] public section

universe u v w

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.SimplicialSites Opposite Functor
open scoped Simplicial DerivedExt

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial

variable {S : Scheme.{u}}

/-- The degree-zero map `a_0 : U.obj (op ⦋0⦌) ⟶ X` of an augmentation. -/
abbrev augmentationZero {X : AlgebraicSpace S} {U : SimplicialObject (AlgebraicSpace S)}
    (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X) :
    U.obj (op ⦋0⦌) ⟶ X :=
  a.app (op ⦋0⦌)

/-- The degree-one map `a_1 : U.obj (op ⦋1⦌) ⟶ X` of an augmentation. -/
abbrev augmentationOne {X : AlgebraicSpace S} {U : SimplicialObject (AlgebraicSpace S)}
    (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X) :
    U.obj (op ⦋1⦌) ⟶ X :=
  a.app (op ⦋1⦌)

/-- The last-vertex map `f_{τ^n_n} : U.obj (op n) ⟶ U.obj (op ⦋0⦌)`. -/
abbrev vertex (U : SimplicialObject (AlgebraicSpace S)) (n : SimplexCategory) :
    U.obj (op n) ⟶ U.obj (op ⦋0⦌) :=
  U.map (op (Sheaf.vertexOp n))

/-- The stage object `K_n = Lf_{τ^n_n}^* K0`. -/
def stageObj {U : SimplicialObject (AlgebraicSpace S)}
    (K0 : DerivedQCoh (U.obj (op ⦋0⦌))) (n : SimplexCategory) :
    ModuleDerived (U.obj (op n)) :=
  (modulePullbackDerived (vertex U n)).obj K0.obj

/-- `stageObj K0 n` is the unbounded derived pullback of `K0` along `vertex U n`. -/
theorem stageObj_eq {U : SimplicialObject (AlgebraicSpace S)}
    (K0 : DerivedQCoh (U.obj (op ⦋0⦌))) (n : SimplexCategory) :
    stageObj K0 n = (modulePullbackDerived (vertex U n)).obj K0.obj :=
  sorry

/-- Recoding of unbounded derived pullback along an equality of morphisms. -/
def recodePullback {Y X : AlgebraicSpace S} {f g : Y ⟶ X} (h : f = g) :
    modulePullbackDerived f ≅ modulePullbackDerived g :=
  eqToIso (congrArg (fun t ↦ modulePullbackDerived t) h)

/-- `recodePullback` is `eqToIso` of `modulePullbackDerived`. -/
theorem recodePullback_eq {Y X : AlgebraicSpace S} {f g : Y ⟶ X} (h : f = g) :
    recodePullback h = eqToIso (congrArg (fun t ↦ modulePullbackDerived t) h) :=
  sorry

/-- The actual iterated pullback object for one pair of cofaces of `U`. -/
abbrev iteratedFaceObj (U : SimplicialObject (AlgebraicSpace S))
    (K0 : ModuleDerived (U.obj (op ⦋0⦌))) (i : Fin 3) (j : Fin 2) :
    ModuleDerived (U.obj (op ⦋2⦌)) :=
  (modulePullbackDerived (U.δ i)).obj ((modulePullbackDerived (U.δ j)).obj K0)

/-- The canonical forward comparison to pullback along the composite coface. -/
def faceComparison (U : SimplicialObject (AlgebraicSpace S))
    (K0 : ModuleDerived (U.obj (op ⦋0⦌))) (i : Fin 3) (j : Fin 2) :
    iteratedFaceObj U K0 i j ⟶
      (modulePullbackDerived (U.δ i ≫ U.δ j)).obj K0 :=
  (modulePullbackDerived.compComparison (U.δ i) (U.δ j)).app K0

/-- `faceComparison` is the component of `modulePullbackDerived.compComparison`. -/
theorem faceComparison_eq (U : SimplicialObject (AlgebraicSpace S))
    (K0 : ModuleDerived (U.obj (op ⦋0⦌))) (i : Fin 3) (j : Fin 2) :
    faceComparison U K0 i j =
      (modulePullbackDerived.compComparison (U.δ i) (U.δ j)).app K0 :=
  sorry

/-- Recoded `C₂` source comparison along `δ 1` then `δ 1`, identified with `δ 2` then `δ 1`. -/
def srcComp11 (U : SimplicialObject (AlgebraicSpace S))
    (K0 : ModuleDerived (U.obj (op ⦋0⦌))) :
    iteratedFaceObj U K0 1 1 ⟶
      (modulePullbackDerived (U.δ (2 : Fin 3) ≫ U.δ (1 : Fin 2))).obj K0 :=
  faceComparison U K0 1 1 ≫
    (recodePullback
        (U.δ_comp_δ_self : U.δ (1 : Fin 3) ≫ U.δ (1 : Fin 2) =
          U.δ (2 : Fin 3) ≫ U.δ (1 : Fin 2))).hom.app K0

/-- `srcComp11` is `faceComparison` recoded along `U.δ_comp_δ_self`. -/
theorem srcComp11_eq (U : SimplicialObject (AlgebraicSpace S))
    (K0 : ModuleDerived (U.obj (op ⦋0⦌))) :
    srcComp11 U K0 =
      faceComparison U K0 1 1 ≫
        (recodePullback
            (U.δ_comp_δ_self : U.δ (1 : Fin 3) ≫ U.δ (1 : Fin 2) =
              U.δ (2 : Fin 3) ≫ U.δ (1 : Fin 2))).hom.app K0 :=
  sorry

/-- Recoded `C₂` comparison along `δ 2` then `δ 0`, identified with `δ 0` then `δ 1`. -/
def tgtComp20 (U : SimplicialObject (AlgebraicSpace S))
    (K0 : ModuleDerived (U.obj (op ⦋0⦌))) :
    iteratedFaceObj U K0 2 0 ⟶
      (modulePullbackDerived (U.δ (0 : Fin 3) ≫ U.δ (1 : Fin 2))).obj K0 :=
  faceComparison U K0 2 0 ≫
    (recodePullback (U.δ_comp_δ (Fin.zero_le (1 : Fin 2)))).hom.app K0

/-- `tgtComp20` is `faceComparison` recoded along `U.δ_comp_δ`. -/
theorem tgtComp20_eq (U : SimplicialObject (AlgebraicSpace S))
    (K0 : ModuleDerived (U.obj (op ⦋0⦌))) :
    tgtComp20 U K0 =
      faceComparison U K0 2 0 ≫
        (recodePullback (U.δ_comp_δ (Fin.zero_le (1 : Fin 2)))).hom.app K0 :=
  sorry

/-- Recoded `C₂` comparison along `δ 0` then `δ 0`, identified with `δ 1` then `δ 0`. -/
def tgtComp00 (U : SimplicialObject (AlgebraicSpace S))
    (K0 : ModuleDerived (U.obj (op ⦋0⦌))) :
    iteratedFaceObj U K0 0 0 ⟶
      (modulePullbackDerived (U.δ (1 : Fin 3) ≫ U.δ (0 : Fin 2))).obj K0 :=
  faceComparison U K0 0 0 ≫
    (recodePullback ((U.δ_comp_δ (le_rfl : (0 : Fin 2) ≤ 0)).symm)).hom.app K0

/-- `tgtComp00` is `faceComparison` recoded along the symmetric `U.δ_comp_δ`. -/
theorem tgtComp00_eq (U : SimplicialObject (AlgebraicSpace S))
    (K0 : ModuleDerived (U.obj (op ⦋0⦌))) :
    tgtComp00 U K0 =
      faceComparison U K0 0 0 ≫
        (recodePullback ((U.δ_comp_δ (le_rfl : (0 : Fin 2) ≤ 0)).symm)).hom.app K0 :=
  sorry

/-- Test-object form of a forward `C₂` cocycle in a category with explicit universes. -/
def forwardCocycleCondition {C : Type v} [Category.{w} C]
    {A₁ B₁ A₂ B₂ A₀ B₀ V₂ V₁ V₀ : C}
    (s₁ : A₁ ⟶ V₂) (t₁ : B₁ ⟶ V₀) (s₂ : A₂ ⟶ V₂) (t₂ : B₂ ⟶ V₁)
    (s₀ : A₀ ⟶ V₁) (t₀ : B₀ ⟶ V₀)
    (u₁ : A₁ ⟶ B₁) (u₂ : A₂ ⟶ B₂) (u₀ : A₀ ⟶ B₀) : Prop :=
  ∀ (W : C) (x₁ : W ⟶ A₁) (x₂ : W ⟶ A₂) (x₀ : W ⟶ A₀),
    x₁ ≫ s₁ = x₂ ≫ s₂ → x₂ ≫ u₂ ≫ t₂ = x₀ ≫ s₀ →
      x₁ ≫ u₁ ≫ t₁ = x₀ ≫ u₀ ≫ t₀

/-- `forwardCocycleCondition` is the test-object matching of the nine maps. -/
theorem forwardCocycleCondition_iff {C : Type v} [Category.{w} C]
    {A₁ B₁ A₂ B₂ A₀ B₀ V₂ V₁ V₀ : C}
    (s₁ : A₁ ⟶ V₂) (t₁ : B₁ ⟶ V₀) (s₂ : A₂ ⟶ V₂) (t₂ : B₂ ⟶ V₁)
    (s₀ : A₀ ⟶ V₁) (t₀ : B₀ ⟶ V₀)
    (u₁ : A₁ ⟶ B₁) (u₂ : A₂ ⟶ B₂) (u₀ : A₀ ⟶ B₀) :
    forwardCocycleCondition s₁ t₁ s₂ t₂ s₀ t₀ u₁ u₂ u₀ ↔
      ∀ (W : C) (x₁ : W ⟶ A₁) (x₂ : W ⟶ A₂) (x₀ : W ⟶ A₀),
        x₁ ≫ s₁ = x₂ ≫ s₂ → x₂ ≫ u₂ ≫ t₂ = x₀ ≫ s₀ →
          x₁ ≫ u₁ ≫ t₁ = x₀ ≫ u₀ ≫ t₀ :=
  sorry

/-- The `C₂` cocycle tested through the canonical forward comparisons on the nine
actual coface maps. No inverse is selected and no invertibility hypothesis is
imposed. -/
def IsCocycle {U : SimplicialObject (AlgebraicSpace S)}
    {K0 : ModuleDerived (U.obj (op ⦋0⦌))}
    (α : (modulePullbackDerived (U.δ (1 : Fin 2))).obj K0 ≅
      (modulePullbackDerived (U.δ (0 : Fin 2))).obj K0) : Prop :=
  forwardCocycleCondition
    (srcComp11 U K0) (faceComparison U K0 1 0)
    (faceComparison U K0 2 1) (tgtComp20 U K0)
    (faceComparison U K0 0 1) (tgtComp00 U K0)
    ((modulePullbackDerived (U.δ (1 : Fin 3))).map α.hom)
    ((modulePullbackDerived (U.δ (2 : Fin 3))).map α.hom)
    ((modulePullbackDerived (U.δ (0 : Fin 3))).map α.hom)

/-- `IsCocycle α` is the forward criterion on the nine coface maps of `α`. -/
theorem isCocycle_iff {U : SimplicialObject (AlgebraicSpace S)}
    {K0 : ModuleDerived (U.obj (op ⦋0⦌))}
    (α : (modulePullbackDerived (U.δ (1 : Fin 2))).obj K0 ≅
      (modulePullbackDerived (U.δ (0 : Fin 2))).obj K0) :
    IsCocycle α ↔
      forwardCocycleCondition
        (srcComp11 U K0) (faceComparison U K0 1 0)
        (faceComparison U K0 2 1) (tgtComp20 U K0)
        (faceComparison U K0 0 1) (tgtComp00 U K0)
        ((modulePullbackDerived (U.δ (1 : Fin 3))).map α.hom)
        ((modulePullbackDerived (U.δ (2 : Fin 3))).map α.hom)
        ((modulePullbackDerived (U.δ (0 : Fin 3))).map α.hom) :=
  sorry

/-- If the three source composition comparisons are invertible, the forward `C₂`
criterion is equivalent to the transported left/right path equality. These
invertibility hypotheses are not part of the glueing theorem. -/
theorem isCocycle_iff_eq {U : SimplicialObject (AlgebraicSpace S)}
    {K0 : ModuleDerived (U.obj (op ⦋0⦌))}
    (α : (modulePullbackDerived (U.δ (1 : Fin 2))).obj K0 ≅
      (modulePullbackDerived (U.δ (0 : Fin 2))).obj K0)
    [h_src1 : IsIso (srcComp11 U K0)]
    [h_src2 : IsIso (faceComparison U K0 2 1)]
    [h_src0 : IsIso (faceComparison U K0 0 1)] :
    IsCocycle α ↔
      inv (srcComp11 U K0) ≫
          (modulePullbackDerived (U.δ (1 : Fin 3))).map α.hom ≫
          faceComparison U K0 1 0 =
        inv (faceComparison U K0 2 1) ≫
          (modulePullbackDerived (U.δ (2 : Fin 3))).map α.hom ≫
          tgtComp20 U K0 ≫
          inv (faceComparison U K0 0 1) ≫
          (modulePullbackDerived (U.δ (0 : Fin 3))).map α.hom ≫
          tgtComp00 U K0 :=
  sorry

/-- Compatibility of a stage-zero isomorphism `e : La_0^* K ≅ K0` with a coface
isomorphism `α`: the two faces of `e` recover `α` after the forward comparisons
of `δ i` then `a_0`, recoded along `a.naturality` to `La_1^* K`. -/
def CompatibleWith {X : AlgebraicSpace S} {U : SimplicialObject (AlgebraicSpace S)}
    (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X) (K : DerivedQCoh X)
    {K0 : ModuleDerived (U.obj (op ⦋0⦌))}
    (e : (modulePullbackDerived (augmentationZero a)).obj K.obj ≅ K0)
    (α : (modulePullbackDerived (U.δ (1 : Fin 2))).obj K0 ≅
      (modulePullbackDerived (U.δ (0 : Fin 2))).obj K0) : Prop :=
  (modulePullbackDerived (U.δ (1 : Fin 2))).map e.hom ≫ α.hom ≫
      (modulePullbackDerived (U.δ (0 : Fin 2))).map e.inv ≫
      (modulePullbackDerived.compComparison (U.δ (0 : Fin 2)) (augmentationZero a)).app
        K.obj ≫
      (recodePullback
          ((a.naturality (op (SimplexCategory.δ (0 : Fin 2)))).trans
            (Category.comp_id (augmentationOne a)))).hom.app
        K.obj =
    (modulePullbackDerived.compComparison (U.δ (1 : Fin 2)) (augmentationZero a)).app
        K.obj ≫
      (recodePullback
          ((a.naturality (op (SimplexCategory.δ (1 : Fin 2)))).trans
            (Category.comp_id (augmentationOne a)))).hom.app
        K.obj

/-- `CompatibleWith` unfolds to the two-face recovery of `α` from `e`. -/
theorem compatibleWith_spec {X : AlgebraicSpace S}
    {U : SimplicialObject (AlgebraicSpace S)}
    (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X) (K : DerivedQCoh X)
    {K0 : ModuleDerived (U.obj (op ⦋0⦌))}
    (e : (modulePullbackDerived (augmentationZero a)).obj K.obj ≅ K0)
    (α : (modulePullbackDerived (U.δ (1 : Fin 2))).obj K0 ≅
      (modulePullbackDerived (U.δ (0 : Fin 2))).obj K0) :
    CompatibleWith a K e α ↔
      (modulePullbackDerived (U.δ (1 : Fin 2))).map e.hom ≫ α.hom ≫
          (modulePullbackDerived (U.δ (0 : Fin 2))).map e.inv ≫
          (modulePullbackDerived.compComparison (U.δ (0 : Fin 2)) (augmentationZero a)).app
            K.obj ≫
          (recodePullback
              ((a.naturality (op (SimplexCategory.δ (0 : Fin 2)))).trans
                (Category.comp_id (augmentationOne a)))).hom.app
            K.obj =
        (modulePullbackDerived.compComparison (U.δ (1 : Fin 2)) (augmentationZero a)).app
            K.obj ≫
          (recodePullback
              ((a.naturality (op (SimplexCategory.δ (1 : Fin 2)))).trans
                (Category.comp_id (augmentationOne a)))).hom.app
            K.obj :=
  sorry

/-- Negative self-Ext vanishing for every vertex pullback `K_n = Lf_{τ^n_n}^* K0`. -/
def NegExtVanishing {U : SimplicialObject (AlgebraicSpace S)}
    (K0 : DerivedQCoh (U.obj (op ⦋0⦌))) : Prop :=
  ∀ (n : SimplexCategory) (i : ℤ), i < 0 →
    Subsingleton (Ext⁽i⁾(stageObj K0 n, stageObj K0 n))

/-- `NegExtVanishing` is vanishing of `Ext⁽i⁾(K_n, K_n)` for all stages `n` and all
`i < 0`. -/
theorem negExtVanishing_iff {U : SimplicialObject (AlgebraicSpace S)}
    (K0 : DerivedQCoh (U.obj (op ⦋0⦌))) :
    NegExtVanishing K0 ↔
      ∀ (n : SimplexCategory) (i : ℤ), i < 0 →
        Subsingleton (Ext⁽i⁾(stageObj K0 n, stageObj K0 n)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Simplicial

end
