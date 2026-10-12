/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.FieldTheory.MvRatFunc.Frobenius
public import ReasLib.RingTheory.DualNumber.Derivation
public import ReasLib.AlgebraicGeometry.FormalDeformation.DualNumber.Pullback
import StacksCheckRecall

/-!
# An inseparable fibre product that is not an object of `C_Λ`

For the embedding `Λ = F_p(t₁,…,tₙ) → k = F_p(x₁,…,xₙ)` sending `tᵢ` to `xᵢ ^ p`,
the first partial derivative defines a section into `k[ε]`. Its algebra pullback
against the constant section is the kernel of that derivative and does not
surject onto `k` through the first projection.
-/

public section

open CategoryTheory TrivSqZeroExt MvRatFunc.Frobenius
open scoped DualNumber

section FunctionField

variable (n p : ℕ) [Fact p.Prime]

#check (MvRatFunc.Frobenius.functionField n p : Type)
#check (MvRatFunc.Frobenius.expandFraction n p : functionField n p →+* functionField n p)
#check (MvRatFunc.Frobenius.baseSubfield n p : Subfield (functionField n p))
#check (MvRatFunc.Frobenius.baseField n p : Type)
#check (MvRatFunc.Frobenius.finite n p : Module.Finite (baseField n p) (functionField n p))

variable (index : Fin n)

#check (MvRatFunc.Frobenius.expandFraction_X n p index :
  expandFraction n p
      (algebraMap (MvPolynomial (Fin n) (ZMod p)) (functionField n p)
        (MvPolynomial.X index)) =
    algebraMap (MvPolynomial (Fin n) (ZMod p)) (functionField n p)
      (MvPolynomial.X index) ^ p)

#check (MvRatFunc.Frobenius.algebraMap_X n p index :
  algebraMap (baseField n p) (functionField n p)
      ((expandFraction n p).rangeRestrictField
        (algebraMap (MvPolynomial (Fin n) (ZMod p)) (functionField n p)
          (MvPolynomial.X index))) =
    algebraMap (MvPolynomial (Fin n) (ZMod p)) (functionField n p)
      (MvPolynomial.X index) ^ p)

#check (MvRatFunc.Frobenius.pderiv n p index :
  Derivation (baseField n p) (functionField n p) (functionField n p))

#check (MvRatFunc.Frobenius.pderiv_algebraMap n p index :
  ∀ polynomial : MvPolynomial (Fin n) (ZMod p),
    pderiv n p index
        (algebraMap (MvPolynomial (Fin n) (ZMod p)) (functionField n p) polynomial) =
      algebraMap (MvPolynomial (Fin n) (ZMod p)) (functionField n p)
        (MvPolynomial.pderiv index polynomial))

#check (MvRatFunc.Frobenius.pderiv_X n p index :
  pderiv n p index
      (algebraMap (MvPolynomial (Fin n) (ZMod p)) (functionField n p)
        (MvPolynomial.X index)) = 1)

variable (other : Fin n) (h_ne : other ≠ index)

#check (MvRatFunc.Frobenius.pderiv_X_of_ne n p h_ne :
  pderiv n p index
      (algebraMap (MvPolynomial (Fin n) (ZMod p)) (functionField n p)
        (MvPolynomial.X other)) = 0)

end FunctionField

section Derivation

variable {Λ k : Type} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k] (D : Derivation Λ k k)

#check (ArtinianLocalAlgCat.residue Λ k : ArtinianLocalAlgCat Λ k)
#check (ArtinianLocalAlgCat.dualNumber Λ k : ArtinianLocalAlgCat Λ k)
#check (D.toDualNumberAlgHom : k →ₐ[Λ] DualNumber k)
#check (ArtinianLocalAlgCat.homOfDerivation D :
  ArtinianLocalAlgCat.residue Λ k ⟶ ArtinianLocalAlgCat.dualNumber Λ k)
#check (ArtinianLocalAlgCat.residueToDualNumber Λ k :
  ArtinianLocalAlgCat.residue Λ k ⟶ ArtinianLocalAlgCat.dualNumber Λ k)

#check (ArtinianLocalAlgCat.homOfDerivation_hom D :
  (ArtinianLocalAlgCat.homOfDerivation D).hom = D.toDualNumberAlgHom)

#check (ArtinianLocalAlgCat.homOfDerivation_apply D :
  ∀ value : k, (ArtinianLocalAlgCat.homOfDerivation D).hom value =
    inl value + inr (D value))

variable (left right : k)

#check (Derivation.mem_dualNumberPullback_iff D (left := left) (right := right) :
  (left, right) ∈ AlgHom.pullback D.toDualNumberAlgHom (inlAlgHom Λ k k) ↔
    left = right ∧ D left = 0)

end Derivation

/- Example 90.3.7: The algebra pullback of the first partial-derivative section and
the constant inclusion into dual numbers does not surject onto the residue field,
so its natural residue map does not make it an object of `C_Λ`. -/
@[stacks 06S4] #check (ArtinianLocalAlgCat.not_surjective_algebraPullback_toResidue :
  ∀ (n p : ℕ) [Fact p.Prime] [NeZero n],
    ¬ Function.Surjective
      (AlgHom.pullbackFst (pderiv n p 0).toDualNumberAlgHom
        (inlAlgHom (baseField n p) (functionField n p) (functionField n p))))
