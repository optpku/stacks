module

public import ReasLib.Algebra.Homology.Koszul.PowerTower.Quotient
import StacksCheckRecall

/-!
# Noetherian powered Koszul towers

@stack 0921
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u v w

variable {A : Type u} [CommRing A] {r : ℕ}

/- Lemma 15.95.1: over a Noetherian ring, the canonical powered-Koszul-to-quotient comparison
is an isomorphism of sequential pro-objects in `D(A)`. -/
section

variable [IsNoetherianRing A]

@[stacks 0921 "powered Koszul quotient pro-isomorphism"]
#check fun (f : Fin r → A) ↦
  (KoszulComplex.PowerTower.Fin.derivedQuotientProComparison_isIso f :
    IsIso (KoszulComplex.PowerTower.Fin.derivedQuotientProComparison f).toHom)

end

/- The source comparison is represented by explicit stage maps, a natural transformation, and
a sequential pro-object morphism. -/
#check fun (f : Fin r → A) (n : ℕ) ↦
  (KoszulComplex.PowerTower.Fin.chainQuotientMap f n :
    KoszulComplex.powerComplex f n ⟶
      (ChainComplex.single₀ (ModuleCat A)).obj
        (KoszulComplex.PowerTower.quotientStage f n))

#check fun (f : Fin r → A) (n : ℕ) ↦
  (KoszulComplex.PowerTower.Fin.derivedQuotientMap f n :
    (KoszulComplex.PowerTower.derivedSystem f).obj (op n) ⟶
      (KoszulComplex.PowerTower.derivedQuotientSystem f).obj (op n))

#check fun (f : Fin r → A) ↦
  (KoszulComplex.PowerTower.Fin.derivedQuotientComparison f :
    KoszulComplex.PowerTower.derivedSystem f ⟶
      KoszulComplex.PowerTower.derivedQuotientSystem f)

#check fun (f : Fin r → A) ↦
  (KoszulComplex.PowerTower.Fin.derivedQuotientProComparison f :
    Pro.SequentialHom
      (KoszulComplex.PowerTower.derivedSystem f)
      (KoszulComplex.PowerTower.derivedQuotientSystem f))

section

variable [IsNoetherianRing A] {C : Type v} [Category.{w} C]

#check fun (f : Fin r → A) (F : DerivedCategory (ModuleCat A) ⥤ C) ↦
  (KoszulComplex.PowerTower.Fin.derivedQuotientProComparison_whiskerRight_isIso f F :
    IsIso
      (Pro.SequentialHom.ofNatTrans
        (Functor.whiskerRight
          (KoszulComplex.PowerTower.Fin.derivedQuotientComparison f) F)).toHom)

end
