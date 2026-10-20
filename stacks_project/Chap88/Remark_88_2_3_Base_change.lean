module

public import ReasLib.Algebra.Category.CommAlgCat.TopologicallyFiniteType.BaseChange.Comparison
import StacksCheckRecall

/-!
# Remark 88.2.3 (Base change)

A ring map carrying a positive power of `I1` into `I2` induces base change on
adic systems. When `I2` is finitely generated, completed tensor product gives
base change on complete algebras. Both constructions commute with passage to
quotient systems; when both ideals are finitely generated, the reconstruction
equivalences identify them.
-/

@[expose] public section

open CategoryTheory

universe u

variable {A1 A2 : Type u} [CommRing A1] [CommRing A2]

#check (AdicAlgebraSystem.baseChange :
  ∀ (φ : A1 →+* A2) (I1 : Ideal A1) (I2 : Ideal A2) {c : ℕ},
    1 ≤ c → Ideal.map φ (I1 ^ c) ≤ I2 →
      AdicAlgebraSystem A1 I1 ⥤ AdicAlgebraSystem A2 I2)

variable [Algebra A1 A2]
variable (I1 : Ideal A1) (I2 : Ideal A2) {c : ℕ} (hc : 1 ≤ c)
variable (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2) (hI2 : I2.FG)

#check (CommAlgCat.TopologicallyFiniteType.baseChange I1 I2 hc hI hI2 :
  CommAlgCat.TopologicallyFiniteType.{u} A1 I1 ⥤
    CommAlgCat.TopologicallyFiniteType.{u} A2 I2)

/- Remark 88.2.3 (Base change)
Systems base change agrees with completed base change after passing to adic
quotient systems. With both ideals finitely generated, the reconstruction
equivalences below give the asserted agreement of the two base-change functors. -/
@[stacks 0AL5] #check
  (CommAlgCat.TopologicallyFiniteType.baseChangeToAdicSystemIso I1 I2 hc hI hI2 :
    CommAlgCat.TopologicallyFiniteType.toAdicSystem I1 ⋙
      AdicAlgebraSystem.baseChange (algebraMap A1 A2) I1 I2 hc
        (by simpa only [Ideal.map_pow] using hI) ≅
    CommAlgCat.TopologicallyFiniteType.baseChange I1 I2 hc hI hI2 ⋙
      CommAlgCat.TopologicallyFiniteType.toAdicSystem I2)

#check (CommAlgCat.TopologicallyFiniteType.baseChangeToAdicSystemIso_app
    I1 I2 hc hI hI2 :
  ∀ B : CommAlgCat.TopologicallyFiniteType.{u} A1 I1,
    (CommAlgCat.TopologicallyFiniteType.baseChangeToAdicSystemIso I1 I2 hc hI hI2).app B =
      CommAlgCat.TopologicallyFiniteType.baseChangeObjIso I1 I2 hc hI hI2 B)

variable (hI1 : I1.FG)

#check (CommAlgCat.TopologicallyFiniteType.baseChangeLimitIso I1 I2 hc hI hI1 hI2 :
  AdicAlgebraSystem.limitFunctor I1 hI1 ⋙
    CommAlgCat.TopologicallyFiniteType.baseChange I1 I2 hc hI hI2 ≅
  AdicAlgebraSystem.baseChange (algebraMap A1 A2) I1 I2 hc
      (by simpa only [Ideal.map_pow] using hI) ⋙
    AdicAlgebraSystem.limitFunctor I2 hI2)

#check (AdicAlgebraSystem.limitFunctorEquivalence I1 hI1 :
  AdicAlgebraSystem A1 I1 ≌ CommAlgCat.TopologicallyFiniteType.{u} A1 I1)

#check (AdicAlgebraSystem.limitFunctorEquivalence I2 hI2 :
  AdicAlgebraSystem A2 I2 ≌ CommAlgCat.TopologicallyFiniteType.{u} A2 I2)
