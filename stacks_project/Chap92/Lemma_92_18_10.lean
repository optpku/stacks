module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CotangentComplex.NaiveComparison
import StacksCheckRecall

/-!
# Comparison of the sheaf cotangent complex with the naive cotangent complex

Lemma 92.18.10 records the canonical cochain map `L(φ) ⟶ NL(B/A)` identifying the naive
cotangent complex with the good truncation `τ_{≥ -1} L(φ)`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open HomologicalComplex
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.CotangentComplex
open scoped SheafOfModules.RingedSite.CotangentComplex

noncomputable section

universe u

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasColimitsOfShape (Discrete WalkingPair) CommRingCat.{u}]

variable {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B)

#check (SheafOfModules.RingedSite.CotangentComplex.toNaive A (Under.mk φ) :
  L(φ) ⟶ NaiveCotangent.obj A (Under.mk φ))

/- Lemma 92.18.10. For a homomorphism `φ : A ⟶ B` of commutative ring sheaves on a site,
the canonical map `L(φ) ⟶ NL_{B/A}` identifies the naive cotangent complex with the good
truncation `τ_{≥ -1} L(φ)`. Its degree-zero component is the canonical presentation
identification; its degree-minus-one component sends `d f ⊗ b` to the class of
`(d₀ f - d₁ f) b` in `I/I²`, and its other components vanish. -/
@[stacks 08US] #check
  (SheafOfModules.RingedSite.CotangentComplex.toNaive_truncGE_quasiIso A (Under.mk φ) :
    QuasiIso (CochainComplex.truncGEMap
      (SheafOfModules.RingedSite.CotangentComplex.toNaive A (Under.mk φ)) (-1)))

#check (SheafOfModules.RingedSite.CotangentComplex.naiveObj_isGE_negOne A (Under.mk φ) :
  (NaiveCotangent.obj A (Under.mk φ)).IsGE (-1))

#check (SheafOfModules.RingedSite.CotangentComplex.toNaive_zero A (Under.mk φ) :
  (SheafOfModules.RingedSite.CotangentComplex.toNaive A (Under.mk φ)).f 0 =
    (objXIso A (Under.mk φ) 0).hom ≫ selfDifferentials A (Under.mk φ))

#check (SheafOfModules.RingedSite.CotangentComplex.toNaive_negOne A (Under.mk φ) :
  (SheafOfModules.RingedSite.CotangentComplex.toNaive A (Under.mk φ)).f (-1) =
    (objXIso A (Under.mk φ) 1).hom ≫ toConormal A (Under.mk φ))

end
end
