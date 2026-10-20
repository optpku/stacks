module

public import ReasLib.CategoryTheory.Adjunction.CosimplicialResolution.Construction
public import ReasLib.AlgebraicTopology.CosimplicialObject.Augmented.ExtraCodegeneracy.Homotopy
public import ReasLib.AlgebraicTopology.CosimplicialObject.Augmented.LastExtraCodegeneracy.Homotopy
public import ReasLib.CategoryTheory.Endofunctor.MonadResolution.ExtraCodegeneracy

/-!
# Contracting cosimplicial resolutions from adjunctions

The adjunction counit supplies the final-coface contraction after postcomposition by the left
adjoint and the zeroth-coface contraction after precomposition by the right adjoint. This leaf
specializes the generic extra-codegeneracy owners and retains the resulting concrete
retractions and structured cosimplicial homotopy equivalences.
-/

@[expose] public section

open CategoryTheory.Functor
open scoped CategoryTheory.IteratedEndofunctor Simplicial

universe uC uD vC vD

namespace CategoryTheory

namespace Adjunction.CosimplicialResolution

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
variable {L : C ⥤ D} {R : D ⥤ C}

/-- The counit-induced retraction of the degree-zero coaugmentation after postcomposition by the
left adjoint. -/
@[stacks 0FKS "degree-zero retraction after applying the left adjoint"]
noncomputable def postcompose.zeroRetraction (adj : L ⊣ R) :
    (postcompose adj).right ^⦋0⦌ ⟶ (postcompose adj).left :=
  (Functor.associator L R L).hom ≫
    Functor.whiskerLeft L adj.counit ≫ (Functor.rightUnitor L).hom

/-- Objectwise, the degree-zero retraction is the adjunction counit at the image under the left
adjoint. -/
@[simp, stacks 0FKS "degree-zero retraction component"]
theorem postcompose.zeroRetraction.app (adj : L ⊣ R) (X : C) :
    (postcompose.zeroRetraction adj).app X = adj.counit.app (L.obj X) := sorry

/-- The counit-induced retraction of the degree-zero coaugmentation after precomposition by the
right adjoint. -/
@[stacks 0FKS "degree-zero retraction after precomposition by the right adjoint"]
noncomputable def precompose.zeroRetraction (adj : L ⊣ R) :
    (precompose adj).right ^⦋0⦌ ⟶ (precompose adj).left :=
  (Functor.associator R L R).inv ≫
    Functor.whiskerRight adj.counit R ≫ (Functor.leftUnitor R).hom

/-- Objectwise, the precomposed degree-zero retraction is obtained by applying the right adjoint
to the adjunction counit. -/
@[simp, stacks 0FKS "precomposed degree-zero retraction component"]
theorem precompose.zeroRetraction.app (adj : L ⊣ R) (X : D) :
    (precompose.zeroRetraction adj).app X = R.map (adj.counit.app X) := sorry

/-- The counit-induced last extra codegeneracy in degree `n` collapses the final `R ⋙ L`
factor. -/
@[stacks 0FKS "last extra codegeneracy after applying the left adjoint"]
noncomputable def postcompose.lastCodegeneracy (adj : L ⊣ R) (n : ℕ) :
    (postcompose adj).right ^⦋n + 1⦌ ⟶ (postcompose adj).right ^⦋n⦌ :=
  (Functor.associator (adj.toMonad.toFunctor ⁺⦋n⦌)
      adj.toMonad.toFunctor L).hom ≫
    Functor.whiskerLeft (adj.toMonad.toFunctor ⁺⦋n⦌)
      (postcompose.zeroRetraction adj)

/-- The degree-zero counit map retracts the postcomposed coaugmentation. -/
@[simp, stacks 0FKS "degree-zero coaugmentation-retraction identity"]
theorem postcompose.zeroRetraction.hom_comp (adj : L ⊣ R) :
    (postcompose adj).hom.app ⦋0⦌ ≫ postcompose.zeroRetraction adj = 𝟙 _ := sorry

/-- The zeroth coface followed by the first last codegeneracy factors through the
coaugmentation and its counit-induced retraction. -/
@[stacks 0FKS "initial relation for the left-adjoint contraction"]
theorem postcompose.lastCodegeneracy.δ₀_comp_s₀ (adj : L ⊣ R) :
    (postcompose adj).right.δ 0 ≫ postcompose.lastCodegeneracy adj 0 =
      postcompose.zeroRetraction adj ≫ (postcompose adj).hom.app ⦋0⦌ := sorry

/-- Every counit-induced last codegeneracy retracts the final coface. -/
@[stacks 0FKS "final-coface relation for the left-adjoint contraction"]
theorem postcompose.lastCodegeneracy.δ_last_comp_s (adj : L ⊣ R) (n : ℕ) :
    (postcompose adj).right.δ (Fin.last (n + 1)) ≫
        postcompose.lastCodegeneracy adj n =
      𝟙 _ := sorry

/-- Counit-induced last codegeneracies commute with all nonfinal cofaces. -/
@[stacks 0FKS "coface relations for the left-adjoint contraction"]
theorem postcompose.lastCodegeneracy.δ_comp_s (adj : L ⊣ R)
    (n : ℕ) (i : Fin (n + 2)) :
    (postcompose adj).right.δ i.castSucc ≫
        postcompose.lastCodegeneracy adj (n + 1) =
      postcompose.lastCodegeneracy adj n ≫ (postcompose adj).right.δ i := sorry

/-- Counit-induced last codegeneracies commute with the ordinary codegeneracies. -/
@[stacks 0FKS "codegeneracy relations for the left-adjoint contraction"]
theorem postcompose.lastCodegeneracy.σ_comp_s (adj : L ⊣ R)
    (n : ℕ) (i : Fin (n + 1)) :
    (postcompose adj).right.σ i.castSucc ≫ postcompose.lastCodegeneracy adj n =
      postcompose.lastCodegeneracy adj (n + 1) ≫
        (postcompose adj).right.σ i := sorry

/-- Applying the left adjoint equips the canonical monad resolution with the last extra
codegeneracy induced by the adjunction counit. -/
@[stacks 0FKS "last extra codegeneracy on the left-adjoint image of a monad resolution"]
noncomputable def postcompose.lastExtraCodegeneracy (adj : L ⊣ R) :
    CosimplicialObject.Augmented.LastExtraCodegeneracy (postcompose adj) where
  s' := postcompose.zeroRetraction adj
  s := postcompose.lastCodegeneracy adj
  η_comp_s' := postcompose.zeroRetraction.hom_comp adj
  δ₀_comp_s₀ := postcompose.lastCodegeneracy.δ₀_comp_s₀ adj
  δ_last_comp_s := postcompose.lastCodegeneracy.δ_last_comp_s adj
  δ_comp_s := postcompose.lastCodegeneracy.δ_comp_s adj
  σ_comp_s := postcompose.lastCodegeneracy.σ_comp_s adj

/-- The retraction stored by the postcomposed last extra codegeneracy is induced by the
adjunction counit. -/
@[simp, stacks 0FKS "retraction of the left-adjoint last extra codegeneracy"]
theorem postcompose.lastExtraCodegeneracy.s' (adj : L ⊣ R) :
    (postcompose.lastExtraCodegeneracy adj).s' =
      postcompose.zeroRetraction adj := sorry

/-- The degreewise maps stored by the postcomposed last extra codegeneracy are the explicit
counit collapses. -/
@[simp, stacks 0FKS "maps of the left-adjoint last extra codegeneracy"]
theorem postcompose.lastExtraCodegeneracy.s (adj : L ⊣ R) (n : ℕ) :
    (postcompose.lastExtraCodegeneracy adj).s n =
      postcompose.lastCodegeneracy adj n := sorry

/-- The extra codegeneracy in degree `n` of the precomposed adjunction resolution collapses the
leading monad factor using the adjunction counit. -/
@[stacks 0FKS "precomposed adjunction-resolution extra codegeneracy"]
noncomputable def precompose.extraCodegeneracyMap (adj : L ⊣ R) (n : ℕ) :
    (precompose adj).right ^⦋n + 1⦌ ⟶ (precompose adj).right ^⦋n⦌ :=
  Functor.whiskerLeft R
      (IteratedEndofunctor.prependIso adj.toMonad.toFunctor n).inv ≫
    (Functor.associator R adj.toMonad.toFunctor
      (adj.toMonad.toFunctor ⁺⦋n⦌)).inv ≫
    Functor.whiskerRight (precompose.zeroRetraction adj)
      (adj.toMonad.toFunctor ⁺⦋n⦌)

/-- Objectwise, the precomposed extra codegeneracy separates the leading monad factor and then
applies the remaining positive iterate to the counit retraction. -/
@[simp, stacks 0FKS "precomposed extra codegeneracy component"]
theorem precompose.extraCodegeneracyMap.app (adj : L ⊣ R) (n : ℕ) (X : D) :
    (precompose.extraCodegeneracyMap adj n).app X =
      (IteratedEndofunctor.prependIso adj.toMonad.toFunctor n).inv.app (R.obj X) ≫
        (adj.toMonad.toFunctor ⁺⦋n⦌).map (R.map (adj.counit.app X)) := sorry

/-- Objectwise, the precomposed extra codegeneracy is the split-unit construction on the
comparison algebra supplied by the adjunction. -/
@[stacks 0FKS "precomposed extra codegeneracy as a split-unit construction"]
theorem precompose.extraCodegeneracyMap.app_eq_splitUnit
    (adj : L ⊣ R) (n : ℕ) (X : D) :
    (precompose.extraCodegeneracyMap adj n).app X =
      Monad.cosimplicialResolution.eval.splitUnit.codegeneracy
        ((Monad.comparison adj).obj X).unitSplitMono n := sorry

/-- The precomposed degree-zero counit map retracts the coaugmentation. -/
@[simp, stacks 0FKS "precomposed degree-zero coaugmentation-retraction identity"]
theorem precompose.zeroRetraction.hom_comp (adj : L ⊣ R) :
    (precompose adj).hom.app ⦋0⦌ ≫ precompose.zeroRetraction adj = 𝟙 _ := sorry

/-- The first coface followed by the first precomposed extra codegeneracy factors through the
coaugmentation and its counit-induced retraction. -/
@[stacks 0FKS "initial relation for the right-adjoint contraction"]
theorem precompose.extraCodegeneracy.δ₁_comp_s₀ (adj : L ⊣ R) :
    (precompose adj).right.δ 1 ≫ precompose.extraCodegeneracyMap adj 0 =
      precompose.zeroRetraction adj ≫ (precompose adj).hom.app ⦋0⦌ := sorry

/-- Every precomposed extra codegeneracy retracts the zeroth coface. -/
@[stacks 0FKS "zeroth-coface relation for the right-adjoint contraction"]
theorem precompose.extraCodegeneracy.δ₀_comp_s (adj : L ⊣ R) (n : ℕ) :
    (precompose adj).right.δ 0 ≫ precompose.extraCodegeneracyMap adj n =
      𝟙 _ := sorry

/-- Precomposed extra codegeneracies commute with all positive cofaces. -/
@[stacks 0FKS "coface relations for the right-adjoint contraction"]
theorem precompose.extraCodegeneracy.δ_comp_s (adj : L ⊣ R)
    (n : ℕ) (i : Fin (n + 2)) :
    (precompose adj).right.δ i.succ ≫
        precompose.extraCodegeneracyMap adj (n + 1) =
      precompose.extraCodegeneracyMap adj n ≫ (precompose adj).right.δ i := sorry

/-- Precomposed extra codegeneracies commute with all positive codegeneracies. -/
@[stacks 0FKS "codegeneracy relations for the right-adjoint contraction"]
theorem precompose.extraCodegeneracy.σ_comp_s (adj : L ⊣ R)
    (n : ℕ) (i : Fin (n + 1)) :
    (precompose adj).right.σ i.succ ≫ precompose.extraCodegeneracyMap adj n =
      precompose.extraCodegeneracyMap adj (n + 1) ≫
        (precompose adj).right.σ i := sorry

/-- Precomposition by the right adjoint equips the canonical monad resolution with the extra
codegeneracy induced by the adjunction counit. -/
@[stacks 0FKS "extra codegeneracy on the precomposed monad resolution"]
noncomputable def precompose.extraCodegeneracy (adj : L ⊣ R) :
    CosimplicialObject.Augmented.ExtraCodegeneracy (precompose adj) where
  s' := precompose.zeroRetraction adj
  s := precompose.extraCodegeneracyMap adj
  η_comp_s' := precompose.zeroRetraction.hom_comp adj
  δ₁_comp_s₀ := precompose.extraCodegeneracy.δ₁_comp_s₀ adj
  δ₀_comp_s := precompose.extraCodegeneracy.δ₀_comp_s adj
  δ_comp_s := precompose.extraCodegeneracy.δ_comp_s adj
  σ_comp_s := precompose.extraCodegeneracy.σ_comp_s adj

/-- The retraction stored by the precomposed extra codegeneracy is induced by the adjunction
counit. -/
@[simp, stacks 0FKS "retraction of the precomposed extra codegeneracy"]
theorem precompose.extraCodegeneracy.s' (adj : L ⊣ R) :
    (precompose.extraCodegeneracy adj).s' = precompose.zeroRetraction adj := sorry

/-- The degreewise maps stored by the precomposed extra codegeneracy are the explicit counit
collapses. -/
@[simp, stacks 0FKS "maps of the precomposed extra codegeneracy"]
theorem precompose.extraCodegeneracy.s (adj : L ⊣ R) (n : ℕ) :
    (precompose.extraCodegeneracy adj).s n =
      precompose.extraCodegeneracyMap adj n := sorry

/-- The canonical cosimplicial retraction of the postcomposed coaugmentation. -/
@[stacks 0FKS "left-adjoint monad-resolution retraction"]
noncomputable def postcompose.inverse (adj : L ⊣ R) :
    (postcompose adj).right ⟶
      (CosimplicialObject.const (C ⥤ D)).obj (postcompose adj).left :=
  (postcompose.lastExtraCodegeneracy adj).retraction

/-- In every cosimplicial degree, the canonical retraction first uses the unique map to degree
zero and then applies the adjunction counit. -/
@[simp, stacks 0FKS "left-adjoint monad-resolution retraction component"]
theorem postcompose.inverse.app (adj : L ⊣ R) (Δ : SimplexCategory) :
    (postcompose.inverse adj).app Δ =
      (postcompose adj).right.map (SimplexCategory.isTerminalZero.from Δ) ≫
        postcompose.zeroRetraction adj := sorry

/-- The degree-zero component of the canonical retraction is the adjunction-counit
retraction. -/
@[simp, stacks 0FKS "left-adjoint monad-resolution retraction in degree zero"]
theorem postcompose.inverse.app_zero (adj : L ⊣ R) :
    (postcompose.inverse adj).app ⦋0⦌ = postcompose.zeroRetraction adj := sorry

/-- The postcomposed coaugmentation followed by its counit-induced retraction is homotopic to
the identity. -/
@[stacks 0FKS "left-adjoint coaugmentation-retraction homotopy"]
theorem postcompose.hom_inv_id (adj : L ⊣ R) :
    CosimplicialObject.DeltaOneHomotopic
      ((postcompose adj).hom ≫ postcompose.inverse adj)
      (𝟙 ((CosimplicialObject.const (C ⥤ D)).obj (postcompose adj).left)) := sorry

/-- The counit-induced retraction followed by the postcomposed coaugmentation is homotopic to
the identity. -/
@[stacks 0FKS "left-adjoint retraction-coaugmentation homotopy"]
theorem postcompose.inv_hom_id (adj : L ⊣ R) :
    CosimplicialObject.DeltaOneHomotopic
      (postcompose.inverse adj ≫ (postcompose adj).hom)
      (𝟙 (postcompose adj).right) := sorry

/-- The left-adjoint image of the monad resolution with its canonical counit-induced homotopy
inverse. -/
@[stacks 0FKS "left-adjoint monad-resolution homotopy equivalence"]
noncomputable def postcompose.homotopyEquiv (adj : L ⊣ R) :
    CosimplicialObject.HomotopyEquiv
      ((CosimplicialObject.const (C ⥤ D)).obj (postcompose adj).left)
      (postcompose adj).right :=
  (postcompose.lastExtraCodegeneracy adj).homotopyEquiv

/-- The forward map of the canonical homotopy equivalence is the postcomposed
coaugmentation. -/
@[simp, stacks 0FKS "forward map of the left-adjoint monad-resolution equivalence"]
theorem postcompose.homotopyEquiv.hom (adj : L ⊣ R) :
    (postcompose.homotopyEquiv adj).hom = (postcompose adj).hom := sorry

/-- The inverse map of the canonical homotopy equivalence is the counit-induced
retraction. -/
@[simp, stacks 0FKS "inverse map of the left-adjoint monad-resolution equivalence"]
theorem postcompose.homotopyEquiv.inv (adj : L ⊣ R) :
    (postcompose.homotopyEquiv adj).inv = postcompose.inverse adj := sorry

/-- Applying the left adjoint makes the canonical monad-resolution coaugmentation a
product-free cosimplicial homotopy equivalence. -/
@[stacks 0FKS "left adjoint contracts the monad resolution"]
theorem postcompose.isHomotopyEquivalence (adj : L ⊣ R) :
    CosimplicialObject.IsHomotopyEquivalence (postcompose adj).hom := sorry

/-- The canonical cosimplicial retraction of the precomposed coaugmentation. -/
@[stacks 0FKS "right-adjoint monad-resolution retraction"]
noncomputable def precompose.inverse (adj : L ⊣ R) :
    (precompose adj).right ⟶
      (CosimplicialObject.const (D ⥤ C)).obj (precompose adj).left :=
  (precompose.extraCodegeneracy adj).retraction

/-- In every cosimplicial degree, the canonical precomposed retraction first uses the unique map
to degree zero and then applies the counit through the right adjoint. -/
@[simp, stacks 0FKS "right-adjoint monad-resolution retraction component"]
theorem precompose.inverse.app (adj : L ⊣ R) (Δ : SimplexCategory) :
    (precompose.inverse adj).app Δ =
      (precompose adj).right.map (SimplexCategory.isTerminalZero.from Δ) ≫
        precompose.zeroRetraction adj := sorry

/-- The degree-zero component of the canonical precomposed retraction is the counit-induced
retraction. -/
@[simp, stacks 0FKS "right-adjoint monad-resolution retraction in degree zero"]
theorem precompose.inverse.app_zero (adj : L ⊣ R) :
    (precompose.inverse adj).app ⦋0⦌ = precompose.zeroRetraction adj := sorry

/-- The precomposed coaugmentation followed by its counit-induced retraction is homotopic to the
identity. -/
@[stacks 0FKS "right-adjoint coaugmentation-retraction homotopy"]
theorem precompose.hom_inv_id (adj : L ⊣ R) :
    CosimplicialObject.DeltaOneHomotopic
      ((precompose adj).hom ≫ precompose.inverse adj)
      (𝟙 ((CosimplicialObject.const (D ⥤ C)).obj (precompose adj).left)) := sorry

/-- The counit-induced precomposed retraction followed by the coaugmentation is homotopic to the
identity. -/
@[stacks 0FKS "right-adjoint retraction-coaugmentation homotopy"]
theorem precompose.inv_hom_id (adj : L ⊣ R) :
    CosimplicialObject.DeltaOneHomotopic
      (precompose.inverse adj ≫ (precompose adj).hom)
      (𝟙 (precompose adj).right) := sorry

/-- The right-adjoint precomposition of the monad resolution with its canonical
counit-induced homotopy inverse. -/
@[stacks 0FKS "right-adjoint monad-resolution homotopy equivalence"]
noncomputable def precompose.homotopyEquiv (adj : L ⊣ R) :
    CosimplicialObject.HomotopyEquiv
      ((CosimplicialObject.const (D ⥤ C)).obj (precompose adj).left)
      (precompose adj).right :=
  (precompose.extraCodegeneracy adj).homotopyEquiv

/-- The forward map of the precomposed homotopy equivalence is the coaugmentation. -/
@[simp, stacks 0FKS "forward map of the right-adjoint monad-resolution equivalence"]
theorem precompose.homotopyEquiv.hom (adj : L ⊣ R) :
    (precompose.homotopyEquiv adj).hom = (precompose adj).hom := sorry

/-- The inverse map of the precomposed homotopy equivalence is the counit-induced
retraction. -/
@[simp, stacks 0FKS "inverse map of the right-adjoint monad-resolution equivalence"]
theorem precompose.homotopyEquiv.inv (adj : L ⊣ R) :
    (precompose.homotopyEquiv adj).inv = precompose.inverse adj := sorry

/-- Precomposition by the right adjoint makes the canonical monad-resolution coaugmentation a
product-free cosimplicial homotopy equivalence. -/
@[stacks 0FKS "right adjoint contracts the monad resolution"]
theorem precompose.isHomotopyEquivalence (adj : L ⊣ R) :
    CosimplicialObject.IsHomotopyEquivalence (precompose adj).hom := sorry

end Adjunction.CosimplicialResolution

end CategoryTheory
