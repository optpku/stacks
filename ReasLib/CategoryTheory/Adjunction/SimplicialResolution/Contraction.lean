/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Adjunction.SimplicialResolution.Construction
public import ReasLib.AlgebraicTopology.SimplicialObject.Augmented.LastExtraDegeneracy.Homotopy
public import ReasLib.CategoryTheory.Endofunctor.ComonadResolution.ExtraDegeneracy

/-!
# Contracting simplicial resolutions from adjunctions

The triangle identities provide canonical sections after composing an adjunction resolution
with either adjoint. This leaf packages the two endpoint conventions as extra degeneracies,
together with their inverses and structured simplicial homotopy equivalences.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.SimplicialObject
open Opposite
open scoped CategoryTheory.IteratedEndofunctor Simplicial

universe uA uS vA vS

namespace CategoryTheory.Adjunction.SimplicialResolution

variable {A : Type uA} {S : Type uS} [Category.{vA} A] [Category.{vS} S]
variable {U : S ⥤ A} {V : A ⥤ S}

/-- The unit-induced section of the degree-zero augmentation after postcomposition by the right
adjoint. -/
@[stacks 08ND "postcomposed resolution zero-section"]
noncomputable def postcompose.zeroSection (adj : U ⊣ V) :
    V ⟶ (postcompose adj).left _⦋0⦌ :=
  V.rightUnitor.inv ≫ V.whiskerLeft adj.unit ≫ (V.associator U V).inv

/-- Objectwise, the postcomposed zero-section is the adjunction unit at the image under the right
adjoint. -/
@[simp, stacks 08ND "postcomposed resolution zero-section component"]
theorem postcompose.zeroSection.app (adj : U ⊣ V) (X : A) :
    (postcompose.zeroSection adj).app X = adj.unit.app (V.obj X) := sorry

/-- The postcomposed zero-section is a strict section of the degree-zero augmentation. -/
@[simp, stacks 08ND "postcomposed resolution zero-section law"]
theorem postcompose.zeroSection.comp_hom_app_zero (adj : U ⊣ V) :
    postcompose.zeroSection adj ≫ (postcompose adj).hom.app (op ⦋0⦌) = 𝟙 V := sorry

/-- The unit-induced section of the degree-zero augmentation after precomposition by the left
adjoint. -/
@[stacks 08ND "precomposed resolution zero-section"]
noncomputable def precompose.zeroSection (adj : U ⊣ V) :
    U ⟶ (precompose adj).left _⦋0⦌ :=
  U.leftUnitor.inv ≫ whiskerRight adj.unit U ≫ (U.associator V U).hom

/-- Objectwise, the precomposed zero-section is obtained by applying the left adjoint to the
adjunction unit. -/
@[simp, stacks 08ND "precomposed resolution zero-section component"]
theorem precompose.zeroSection.app (adj : U ⊣ V) (X : S) :
    (precompose.zeroSection adj).app X = U.map (adj.unit.app X) := sorry

/-- The precomposed zero-section is a strict section of the degree-zero augmentation. -/
@[simp, stacks 08ND "precomposed resolution zero-section law"]
theorem precompose.zeroSection.comp_hom_app_zero (adj : U ⊣ V) :
    precompose.zeroSection adj ≫ (precompose adj).hom.app (op ⦋0⦌) = 𝟙 U := sorry

/-- The last extra degeneracy in degree `n` of the postcomposed adjunction resolution inserts the
adjunction unit after the final copy of the right adjoint. -/
@[stacks 08ND "postcomposed adjunction-resolution last degeneracy"]
noncomputable def postcompose.lastDegeneracy (adj : U ⊣ V) (n : ℕ) :
    (postcompose adj).left _⦋n⦌ ⟶ (postcompose adj).left _⦋n + 1⦌ :=
  Functor.whiskerLeft (adj.toComonad.toFunctor ⁺⦋n⦌)
      (postcompose.zeroSection adj) ≫
    (Functor.associator (adj.toComonad.toFunctor ⁺⦋n⦌)
      adj.toComonad.toFunctor V).inv

/-- The first postcomposed last degeneracy followed by the zeroth face factors through the
augmentation and its unit-induced section. -/
@[stacks 08ND "initial relation for the postcomposed last degeneracy"]
theorem postcompose.lastDegeneracy.s₀_comp_δ₀ (adj : U ⊣ V) :
    postcompose.lastDegeneracy adj 0 ≫ (postcompose adj).left.δ 0 =
      (postcompose adj).hom.app (op ⦋0⦌) ≫ postcompose.zeroSection adj := sorry

/-- Every postcomposed last degeneracy is a section of the final face. -/
@[stacks 08ND "final-face relation for the postcomposed last degeneracy"]
theorem postcompose.lastDegeneracy.s_comp_δ_last (adj : U ⊣ V) (n : ℕ) :
    postcompose.lastDegeneracy adj n ≫
        (postcompose adj).left.δ (Fin.last (n + 1)) =
      𝟙 _ := sorry

/-- Postcomposed last degeneracies commute with all nonfinal faces. -/
@[stacks 08ND "face relations for the postcomposed last degeneracy"]
theorem postcompose.lastDegeneracy.s_comp_δ (adj : U ⊣ V)
    (n : ℕ) (i : Fin (n + 2)) :
    postcompose.lastDegeneracy adj (n + 1) ≫
        (postcompose adj).left.δ i.castSucc =
      (postcompose adj).left.δ i ≫ postcompose.lastDegeneracy adj n := sorry

/-- Postcomposed last degeneracies commute with the ordinary degeneracies. -/
@[stacks 08ND "degeneracy relations for the postcomposed last degeneracy"]
theorem postcompose.lastDegeneracy.s_comp_σ (adj : U ⊣ V)
    (n : ℕ) (i : Fin (n + 1)) :
    postcompose.lastDegeneracy adj n ≫ (postcompose adj).left.σ i.castSucc =
      (postcompose adj).left.σ i ≫
        postcompose.lastDegeneracy adj (n + 1) := sorry

/-- Postcomposition by the right adjoint equips the canonical comonad resolution with the last
extra degeneracy induced by the adjunction unit. -/
@[stacks 08ND "last extra degeneracy on the postcomposed adjunction resolution"]
noncomputable def postcompose.lastExtraDegeneracy (adj : U ⊣ V) :
    SimplicialObject.Augmented.LastExtraDegeneracy (postcompose adj) where
  s' := postcompose.zeroSection adj
  s := postcompose.lastDegeneracy adj
  s'_comp_ε := postcompose.zeroSection.comp_hom_app_zero adj
  s₀_comp_δ₀ := postcompose.lastDegeneracy.s₀_comp_δ₀ adj
  s_comp_δ_last := postcompose.lastDegeneracy.s_comp_δ_last adj
  s_comp_δ := postcompose.lastDegeneracy.s_comp_δ adj
  s_comp_σ := postcompose.lastDegeneracy.s_comp_σ adj

/-- The section stored by the postcomposed last extra degeneracy is the unit-induced
zero-section. -/
@[simp, stacks 08ND "section of the postcomposed last extra degeneracy"]
theorem postcompose.lastExtraDegeneracy.s' (adj : U ⊣ V) :
    (postcompose.lastExtraDegeneracy adj).s' = postcompose.zeroSection adj := sorry

/-- The maps stored by the postcomposed last extra degeneracy are the explicit unit
insertions. -/
@[simp, stacks 08ND "maps of the postcomposed last extra degeneracy"]
theorem postcompose.lastExtraDegeneracy.s (adj : U ⊣ V) (n : ℕ) :
    (postcompose.lastExtraDegeneracy adj).s n =
      postcompose.lastDegeneracy adj n := sorry

/-- The extra degeneracy in degree `n` of the precomposed adjunction resolution inserts the
adjunction unit before the iterated comonad factors. -/
@[stacks 08ND "precomposed adjunction-resolution extra degeneracy"]
noncomputable def precompose.extraDegeneracyMap (adj : U ⊣ V) (n : ℕ) :
    (precompose adj).left _⦋n⦌ ⟶ (precompose adj).left _⦋n + 1⦌ :=
  Functor.whiskerRight (precompose.zeroSection adj)
      (adj.toComonad.toFunctor ⁺⦋n⦌) ≫
    (Functor.associator U adj.toComonad.toFunctor
      (adj.toComonad.toFunctor ⁺⦋n⦌)).hom ≫
    Functor.whiskerLeft U
      (IteratedEndofunctor.prependIso adj.toComonad.toFunctor n).hom

/-- Objectwise, the precomposed extra degeneracy is the split-counit construction on the
comparison coalgebra supplied by the adjunction. -/
@[simp, stacks 08ND "precomposed extra degeneracy as a split-counit construction"]
theorem precompose.extraDegeneracyMap.app (adj : U ⊣ V) (n : ℕ) (X : S) :
    (precompose.extraDegeneracyMap adj n).app X =
      Comonad.simplicialResolution.eval.splitCounit.degeneracy
        ((Comonad.comparison adj).obj X).counitSplitEpi n := sorry

/-- The first precomposed extra degeneracy followed by the last face factors through the
augmentation and its unit-induced section. -/
@[stacks 08ND "initial relation for the precomposed extra degeneracy"]
theorem precompose.extraDegeneracy.s₀_comp_δ₁ (adj : U ⊣ V) :
    precompose.extraDegeneracyMap adj 0 ≫ (precompose adj).left.δ 1 =
      (precompose adj).hom.app (op ⦋0⦌) ≫ precompose.zeroSection adj := sorry

/-- Every precomposed extra degeneracy is a section of the zeroth face. -/
@[stacks 08ND "zeroth-face relation for the precomposed extra degeneracy"]
theorem precompose.extraDegeneracy.s_comp_δ₀ (adj : U ⊣ V) (n : ℕ) :
    precompose.extraDegeneracyMap adj n ≫ (precompose adj).left.δ 0 = 𝟙 _ := sorry

/-- Precomposed extra degeneracies commute with the remaining faces. -/
@[stacks 08ND "face relations for the precomposed extra degeneracy"]
theorem precompose.extraDegeneracy.s_comp_δ (adj : U ⊣ V)
    (n : ℕ) (i : Fin (n + 2)) :
    precompose.extraDegeneracyMap adj (n + 1) ≫
        (precompose adj).left.δ i.succ =
      (precompose adj).left.δ i ≫ precompose.extraDegeneracyMap adj n := sorry

/-- Precomposed extra degeneracies commute with the ordinary degeneracies. -/
@[stacks 08ND "degeneracy relations for the precomposed extra degeneracy"]
theorem precompose.extraDegeneracy.s_comp_σ (adj : U ⊣ V)
    (n : ℕ) (i : Fin (n + 1)) :
    precompose.extraDegeneracyMap adj n ≫ (precompose adj).left.σ i.succ =
      (precompose adj).left.σ i ≫
        precompose.extraDegeneracyMap adj (n + 1) := sorry

/-- Precomposition by the left adjoint equips the canonical comonad resolution with the extra
degeneracy induced by the adjunction unit. -/
@[stacks 08ND "extra degeneracy on the precomposed adjunction resolution"]
noncomputable def precompose.extraDegeneracy (adj : U ⊣ V) :
    SimplicialObject.Augmented.ExtraDegeneracy (precompose adj) where
  s' := precompose.zeroSection adj
  s := precompose.extraDegeneracyMap adj
  s'_comp_ε := precompose.zeroSection.comp_hom_app_zero adj
  s₀_comp_δ₁ := precompose.extraDegeneracy.s₀_comp_δ₁ adj
  s_comp_δ₀ := precompose.extraDegeneracy.s_comp_δ₀ adj
  s_comp_δ := precompose.extraDegeneracy.s_comp_δ adj
  s_comp_σ := precompose.extraDegeneracy.s_comp_σ adj

/-- The section stored by the precomposed extra degeneracy is the unit-induced zero-section. -/
@[simp, stacks 08ND "section of the precomposed extra degeneracy"]
theorem precompose.extraDegeneracy.s' (adj : U ⊣ V) :
    (precompose.extraDegeneracy adj).s' = precompose.zeroSection adj := sorry

/-- The maps stored by the precomposed extra degeneracy are the explicit unit insertions. -/
@[simp, stacks 08ND "maps of the precomposed extra degeneracy"]
theorem precompose.extraDegeneracy.s (adj : U ⊣ V) (n : ℕ) :
    (precompose.extraDegeneracy adj).s n =
      precompose.extraDegeneracyMap adj n := sorry

/-- The simplicial inverse of the postcomposed augmentation induced by its zero-section. -/
@[stacks 08ND "postcomposed resolution inverse"]
noncomputable def postcompose.inverse (adj : U ⊣ V) :
    (const (A ⥤ S)).obj V ⟶ (postcompose adj).left :=
  (postcompose.lastExtraDegeneracy adj).section_

/-- In every simplicial degree, the postcomposed inverse is its zero-section followed by the
unique simplex operator from degree zero. -/
@[simp, stacks 08ND "postcomposed resolution inverse component"]
theorem postcompose.inverse.app (adj : U ⊣ V) (Δ : SimplexCategoryᵒᵖ) :
    (postcompose.inverse adj).app Δ =
      postcompose.zeroSection adj ≫
        (postcompose adj).left.map
          (SimplexCategory.isTerminalZero.from (unop Δ)).op := sorry

/-- The degree-zero component of the postcomposed inverse is its defining zero-section. -/
@[simp, stacks 08ND "postcomposed resolution inverse in degree zero"]
theorem postcompose.inverse.app_zero (adj : U ⊣ V) :
    (postcompose.inverse adj).app (op ⦋0⦌) = postcompose.zeroSection adj := sorry

/-- Evaluating a component of the postcomposed inverse gives the unit component followed by the
corresponding simplicial structure map. -/
@[simp, stacks 08ND "evaluated postcomposed resolution inverse component"]
theorem postcompose.inverse.app_app (adj : U ⊣ V)
    (Δ : SimplexCategoryᵒᵖ) (X : A) :
    ((postcompose.inverse adj).app Δ).app X =
      adj.unit.app (V.obj X) ≫
        ((postcompose adj).left.map
          (SimplexCategory.isTerminalZero.from (unop Δ)).op).app X := sorry

/-- The canonical postcomposed inverse is a strict right inverse to the augmentation. -/
@[simp, stacks 08ND "postcomposed resolution inverse law"]
theorem postcompose.inverse.comp_hom (adj : U ⊣ V) :
    postcompose.inverse adj ≫ (postcompose adj).hom =
      𝟙 ((const (A ⥤ S)).obj V) := sorry

/-- The simplicial inverse of the precomposed augmentation induced by its zero-section. -/
@[stacks 08ND "precomposed resolution inverse"]
noncomputable def precompose.inverse (adj : U ⊣ V) :
    (const (S ⥤ A)).obj U ⟶ (precompose adj).left :=
  (precompose.extraDegeneracy adj).section_

/-- In every simplicial degree, the precomposed inverse is its zero-section followed by the
unique simplex operator from degree zero. -/
@[simp, stacks 08ND "precomposed resolution inverse component"]
theorem precompose.inverse.app (adj : U ⊣ V) (Δ : SimplexCategoryᵒᵖ) :
    (precompose.inverse adj).app Δ =
      precompose.zeroSection adj ≫
        (precompose adj).left.map
          (SimplexCategory.isTerminalZero.from (unop Δ)).op := sorry

/-- The degree-zero component of the precomposed inverse is its defining zero-section. -/
@[simp, stacks 08ND "precomposed resolution inverse in degree zero"]
theorem precompose.inverse.app_zero (adj : U ⊣ V) :
    (precompose.inverse adj).app (op ⦋0⦌) = precompose.zeroSection adj := sorry

/-- Evaluating a component of the precomposed inverse applies the left adjoint to the unit and
then follows the corresponding simplicial structure map. -/
@[simp, stacks 08ND "evaluated precomposed resolution inverse component"]
theorem precompose.inverse.app_app (adj : U ⊣ V)
    (Δ : SimplexCategoryᵒᵖ) (X : S) :
    ((precompose.inverse adj).app Δ).app X =
      U.map (adj.unit.app X) ≫
        ((precompose adj).left.map
          (SimplexCategory.isTerminalZero.from (unop Δ)).op).app X := sorry

/-- The canonical precomposed inverse is a strict right inverse to the augmentation. -/
@[simp, stacks 08ND "precomposed resolution inverse law"]
theorem precompose.inverse.comp_hom (adj : U ⊣ V) :
    precompose.inverse adj ≫ (precompose adj).hom =
      𝟙 ((const (S ⥤ A)).obj U) := sorry

/-- The augmentation followed by its unit-induced inverse is homotopic to the identity.  This is
the postcomposed specialization of the canonical pre/postcomposition interchange homotopy. -/
@[stacks 08ND "postcomposed resolution augmentation-section homotopy"]
theorem postcompose.hom_inv_id (adj : U ⊣ V) :
    Homotopic
      ((postcompose adj).hom ≫ postcompose.inverse adj)
      (𝟙 (postcompose adj).left) := sorry

/-- The unit-induced inverse followed by the augmentation is homotopic to the identity.  In fact,
the composite is already the strict identity by `postcompose.inverse.comp_hom`. -/
@[stacks 08ND "postcomposed resolution section-augmentation homotopy"]
theorem postcompose.inv_hom_id (adj : U ⊣ V) :
    Homotopic
      (postcompose.inverse adj ≫ (postcompose adj).hom)
      (𝟙 ((const (A ⥤ S)).obj V)) := sorry

/-- The postcomposed adjunction resolution with its canonical unit-induced homotopy inverse. -/
@[stacks 08ND "postcomposed resolution homotopy equivalence"]
noncomputable def postcompose.homotopyEquiv (adj : U ⊣ V) :
    HomotopyEquiv (postcompose adj).left ((const (A ⥤ S)).obj V) :=
  (postcompose.lastExtraDegeneracy adj).simplicialHomotopyEquiv

/-- The precomposed adjunction resolution with its canonical unit-induced homotopy inverse. -/
@[stacks 08ND "precomposed resolution homotopy equivalence"]
noncomputable def precompose.homotopyEquiv (adj : U ⊣ V) :
    HomotopyEquiv (precompose adj).left ((const (S ⥤ A)).obj U) :=
  (precompose.extraDegeneracy adj).simplicialHomotopyEquiv

/-- The forward map of the canonical postcomposed homotopy equivalence is the resolution
augmentation. -/
@[simp, stacks 08ND "forward map of the postcomposed resolution equivalence"]
theorem postcompose.homotopyEquiv.hom (adj : U ⊣ V) :
    (postcompose.homotopyEquiv adj).hom = (postcompose adj).hom := sorry

/-- The inverse map of the canonical postcomposed homotopy equivalence is induced by the
adjunction unit. -/
@[simp, stacks 08ND "inverse map of the postcomposed resolution equivalence"]
theorem postcompose.homotopyEquiv.inv (adj : U ⊣ V) :
    (postcompose.homotopyEquiv adj).inv = postcompose.inverse adj := sorry

/-- The forward map of the canonical precomposed homotopy equivalence is the resolution
augmentation. -/
@[simp, stacks 08ND "forward map of the precomposed resolution equivalence"]
theorem precompose.homotopyEquiv.hom (adj : U ⊣ V) :
    (precompose.homotopyEquiv adj).hom = (precompose adj).hom := sorry

/-- The inverse map of the canonical precomposed homotopy equivalence is induced by the
adjunction unit. -/
@[simp, stacks 08ND "inverse map of the precomposed resolution equivalence"]
theorem precompose.homotopyEquiv.inv (adj : U ⊣ V) :
    (precompose.homotopyEquiv adj).inv = precompose.inverse adj := sorry

/-- The precomposed augmentation followed by its unit-induced inverse is homotopic to the
identity. -/
@[stacks 08ND "precomposed resolution augmentation-section homotopy"]
theorem precompose.hom_inv_id (adj : U ⊣ V) :
    Homotopic
      ((precompose adj).hom ≫ precompose.inverse adj)
      (𝟙 (precompose adj).left) := sorry

/-- The unit-induced inverse followed by the precomposed augmentation is homotopic to the
identity. In fact, this composite is strict by `precompose.inverse.comp_hom`. -/
@[stacks 08ND "precomposed resolution section-augmentation homotopy"]
theorem precompose.inv_hom_id (adj : U ⊣ V) :
    Homotopic
      (precompose.inverse adj ≫ (precompose adj).hom)
      (𝟙 ((const (S ⥤ A)).obj U)) := sorry

/-- Postcomposing the adjunction resolution by the right adjoint makes its augmentation a
simplicial homotopy equivalence. -/
@[stacks 08ND "postcomposed augmentation is a homotopy equivalence"]
theorem postcompose.isHomotopyEquivalence (adj : U ⊣ V) :
    IsHomotopyEquivalence (postcompose adj).hom := sorry

/-- Precomposing the adjunction resolution by the left adjoint makes its augmentation a
simplicial homotopy equivalence. -/
@[stacks 08ND "precomposed augmentation is a homotopy equivalence"]
theorem precompose.isHomotopyEquivalence (adj : U ⊣ V) :
    IsHomotopyEquivalence (precompose adj).hom := sorry

end CategoryTheory.Adjunction.SimplicialResolution
