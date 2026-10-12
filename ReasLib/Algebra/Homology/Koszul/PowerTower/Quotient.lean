/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.Koszul.PowerTower
public import ReasLib.CategoryTheory.Pro.Sequential.Isomorphism
import Mathlib.Tactic.CrossRefAttribute

/-!
# Powered Koszul towers and their quotient towers

For a finite tuple `f`, the powered Koszul complex maps canonically to the quotient by the
corresponding powered-family ideal. This leaf packages those stage maps into a morphism of
sequential derived towers and records its Noetherian pro-isomorphism theorem.

@stack 0921
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u v w

namespace KoszulComplex.PowerTower.Fin

variable {A : Type u} [CommRing A] {r : ℕ}

/-- The canonical chain map from a powered Koszul stage to its powered-family quotient in
degree zero. -/
@[stacks 0921 "powered Koszul chain quotient comparison"]
abbrev chainQuotientMap (f : Fin r → A) (n : ℕ) :
    KoszulComplex.powerComplex f n ⟶
      (ChainComplex.single₀ (ModuleCat A)).obj (quotientStage f n) :=
  (ChainComplex.toSingle₀Equiv
    (KoszulComplex.powerComplex f n) (quotientStage f n)).symm
      ⟨zeroQuotientMap f n, firstDifferential_zeroQuotientMap f n⟩

/-- The canonical morphism in `D(A)` from a powered Koszul stage to its powered-family quotient
in degree zero. -/
@[stacks 0921 "derived powered Koszul stage quotient comparison"]
abbrev derivedQuotientMap (f : Fin r → A) (n : ℕ) :
    (derivedSystem f).obj (op n) ⟶ (derivedQuotientSystem f).obj (op n) :=
  DerivedCategory.Q.map
      (HomologicalComplex.extendMap
        (chainQuotientMap f n) ComplexShape.embeddingDownNat) ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat
        (quotientStage f n) (0 : ℕ) (0 : ℤ) rfl).hom) ≫
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app
      (quotientStage f n)).inv

/-- The derived powered-Koszul-to-quotient maps commute with adjacent tower transitions. -/
@[stacks 0921 "naturality of the powered Koszul quotient comparison"]
theorem derivedQuotientMap_naturality (f : Fin r → A) (n : ℕ) :
    (derivedSystem f).map (homOfLE (Nat.le_succ n)).op ≫ derivedQuotientMap f n =
      derivedQuotientMap f (n + 1) ≫
        (derivedQuotientSystem f).map (homOfLE (Nat.le_succ n)).op := sorry
-- Proof strategy: unfold the two derived stage maps, use naturality of the powered Koszul
-- quotient chain maps, and simplify the `Q.map` and extended-single comparison compositions.

/-- The canonical natural transformation from the powered Koszul derived tower to the
powered-family quotient derived tower. -/
@[stacks 0921 "powered Koszul quotient comparison morphism"]
noncomputable def derivedQuotientComparison (f : Fin r → A) :
    derivedSystem f ⟶ derivedQuotientSystem f :=
  NatTrans.ofOpSequence (derivedQuotientMap f) (derivedQuotientMap_naturality f)

/-- The component of the powered Koszul quotient comparison is the explicit stage map. -/
@[simp, stacks 0921 "powered Koszul quotient comparison component"]
theorem derivedQuotientComparison_app (f : Fin r → A) (n : ℕ) :
    (derivedQuotientComparison f).app (op n) = derivedQuotientMap f n := sorry
-- Proof strategy: unfold `derivedQuotientComparison` and use the component formula for
-- `NatTrans.ofOpSequence`.

/-- The sequential representative of the canonical powered-Koszul-to-quotient comparison. -/
@[stacks 0921 "powered Koszul quotient sequential representative"]
noncomputable abbrev derivedQuotientProComparison (f : Fin r → A) :
    Pro.SequentialHom (derivedSystem f) (derivedQuotientSystem f) :=
  Pro.SequentialHom.ofNatTrans (derivedQuotientComparison f)

/-- Lemma 15.95.1 (Stacks `0921`): over a Noetherian ring, the canonical comparison from the
powered Koszul tower to the powered-family quotient tower is an isomorphism of pro-objects in
`D(A)`. Stage `n` here represents the textbook exponent `n + 1`. -/
@[stacks 0921]
theorem derivedQuotientProComparison_isIso [IsNoetherianRing A] (f : Fin r → A) :
    IsIso (derivedQuotientProComparison f).toHom := sorry
-- Proof strategy: apply the Noetherian Artin-Rees comparison for powered Koszul homology;
-- it makes every homology pro-kernel and pro-cokernel zero, hence the sequential pro-map is an iso.

/-- Applying any functor stagewise preserves the Noetherian powered-Koszul quotient
pro-isomorphism. -/
@[stacks 0921 "functorial powered Koszul quotient pro-isomorphism"]
theorem derivedQuotientProComparison_whiskerRight_isIso
    [IsNoetherianRing A] {C : Type v} [Category.{w} C]
    (f : Fin r → A) (F : DerivedCategory (ModuleCat A) ⥤ C) :
    IsIso
      (Pro.SequentialHom.ofNatTrans
        (Functor.whiskerRight (derivedQuotientComparison f) F)).toHom := sorry
-- Proof strategy: identify the displayed map with the image of
-- `derivedQuotientProComparison f` under the induced pro-functor and use preservation of isomorphisms.

end KoszulComplex.PowerTower.Fin
