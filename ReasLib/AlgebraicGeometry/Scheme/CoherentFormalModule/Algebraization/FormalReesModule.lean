module

public import ReasLib.RingTheory.LocalCohomology.PolynomialModuleLift
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Category
public import ReasLib.AlgebraicGeometry.Scheme.Module.IdealPower.Product
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Sections
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.GradedObject
public import Mathlib.Data.Finsupp.Multiset

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped BigOperators

universe u

namespace AlgebraicGeometry.Scheme.Modules.FormalReesModule

/-- The graded sheaf whose degree-`n` part is `J ^ (n * c) M`. -/
noncomputable abbrev powered {X : Scheme.{u}} (J : X.IdealSheafData)
    (M : X.Modules) (c : ℕ) : GradedObject ℕ X.Modules :=
  fun n ↦ (idealPowerProductSubobject J M (n * c) : X.Modules)

/-- The standard graded polynomial-module sheaf on `r` variables with coefficient sheaf `M`. -/
noncomputable abbrev polynomial {X : Scheme.{u}} (r : ℕ) (M : X.Modules) :
    GradedObject ℕ X.Modules :=
  fun n ↦ ∐ fun _ : Sym (Fin r) n ↦ M

/-- The monomial in `I ^ n` determined by a symmetric word in the chosen generators. -/
theorem monomialCoefficient_mem {A : Type u} [CommRing A] {r n : ℕ}
    (I : Ideal A) (a : Fin r → I) (d : Sym (Fin r) n) :
    ∏ j, (a j : A) ^ ((Sym.equivNatSum (Fin r) n d : Fin r →₀ ℕ) j) ∈ I ^ n := sorry

/-- The coefficient in `I ^ n` represented by a symmetric monomial in the chosen generators. -/
noncomputable def monomialCoefficient {A : Type u} [CommRing A] {r n : ℕ}
    (I : Ideal A) (a : Fin r → I) (d : Sym (Fin r) n) : (I ^ n : Ideal A) :=
  ⟨∏ j, (a j : A) ^ ((Sym.equivNatSum (Fin r) n d : Fin r →₀ ℕ) j),
    monomialCoefficient_mem I a d⟩

/-- The underlying element of a monomial coefficient is the corresponding product of powers. -/
theorem monomialCoefficient_coe {A : Type u} [CommRing A] {r n : ℕ}
    (I : Ideal A) (a : Fin r → I) (d : Sym (Fin r) n) :
    (monomialCoefficient I a d : A) =
      ∏ j, (a j : A) ^ ((Sym.equivNatSum (Fin r) n d : Fin r →₀ ℕ) j) := sorry

/-- Multiplication by a coefficient in `I ^ m` factors through `J ^ m M`. -/
theorem coefficientAction_factors {A : Type u} [CommRing A] (I : Ideal A)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) (M : X.Modules)
    {m : ℕ} (g : (I ^ m : Ideal A)) :
    (idealPowerProductSubobject ((Scheme.idealSheafDataOfIdealOnSpec I).comap f) M m).Factors
      (RingedSpace.globalSectionMul ((Scheme.Hom.globalSectionsMap f) g.1) M) := sorry

/-- Multiplication by `g ∈ I ^ m`, factored through the sheaf submodule `J ^ m M`. -/
noncomputable def coefficientAction {A : Type u} [CommRing A] (I : Ideal A)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) (M : X.Modules)
    {m : ℕ} (g : (I ^ m : Ideal A)) :
    M ⟶ (idealPowerProductSubobject
      ((Scheme.idealSheafDataOfIdealOnSpec I).comap f) M m : X.Modules) :=
  (idealPowerProductSubobject
      ((Scheme.idealSheafDataOfIdealOnSpec I).comap f) M m).factorThru
    (RingedSpace.globalSectionMul ((Scheme.Hom.globalSectionsMap f) g.1) M)
    (coefficientAction_factors I f M g)

/-- The coefficient action followed by the ideal-power inclusion is multiplication by the
corresponding global coefficient. -/
theorem coefficientAction_arrow {A : Type u} [CommRing A] (I : Ideal A)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) (M : X.Modules)
    {m : ℕ} (g : (I ^ m : Ideal A)) :
    coefficientAction I f M g ≫
        (idealPowerProductSubobject
          ((Scheme.idealSheafDataOfIdealOnSpec I).comap f) M m).arrow =
      RingedSpace.globalSectionMul ((Scheme.Hom.globalSectionsMap f) g.1) M := sorry

/-- Multiplication by a homogeneous polynomial, placed in the matching symmetric-monomial
summands of the polynomial-module sheaf. -/
noncomputable def homogeneousAction {A : Type u} [CommRing A] {r n : ℕ}
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) (M : X.Modules)
    (p : MvPolynomial.standardGrading (Fin r) A n) : M ⟶ polynomial r M n :=
  ∑ d ∈ p.1.support,
    if h : d.sum (fun _ e ↦ e) = n then
      RingedSpace.globalSectionMul
          ((Scheme.Hom.globalSectionsMap f) (MvPolynomial.coeff d p.1)) M ≫
        Sigma.ι (fun _ : Sym (Fin r) n ↦ M)
          ((Sym.equivNatSum (Fin r) n).symm ⟨d, h⟩)
    else 0

/-- The homogeneous action is the sum of coefficient multiplications into the corresponding
symmetric-monomial summands. -/
theorem homogeneousAction_monomial {A : Type u} [CommRing A] {r n : ℕ}
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) (M : X.Modules)
    (p : MvPolynomial.standardGrading (Fin r) A n) :
    homogeneousAction f M p =
      ∑ d ∈ p.1.support,
        if h : d.sum (fun _ e ↦ e) = n then
          RingedSpace.globalSectionMul
              ((Scheme.Hom.globalSectionsMap f) (MvPolynomial.coeff d p.1)) M ≫
            Sigma.ι (fun _ : Sym (Fin r) n ↦ M)
              ((Sym.equivNatSum (Fin r) n).symm ⟨d, h⟩)
        else 0 := sorry

/-- Evaluation `T_j ↦ a_j` from the polynomial-module sheaf to the ordinary Rees-module
sheaf. -/
noncomputable def evaluation {A : Type u} [CommRing A] {r : ℕ}
    (I : Ideal A) (a : Fin r → I) {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (M : X.Modules) :
    polynomial r M ⟶
      powered ((Scheme.idealSheafDataOfIdealOnSpec I).comap f) M 1 :=
  fun n ↦ Sigma.desc fun d : Sym (Fin r) n ↦
    coefficientAction I f M (monomialCoefficient I a d) ≫
      eqToHom (congrArg
        (fun k ↦
          (idealPowerProductSubobject
            ((Scheme.idealSheafDataOfIdealOnSpec I).comap f) M k : X.Modules))
        (Nat.mul_one n).symm)

/-- Evaluation on a monomial summand is multiplication by the corresponding monomial in the
chosen generators. -/
theorem evaluation_ι {A : Type u} [CommRing A] {r n : ℕ}
    (I : Ideal A) (a : Fin r → I) {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (M : X.Modules) (d : Sym (Fin r) n) :
    Sigma.ι (fun _ : Sym (Fin r) n ↦ M) d ≫ evaluation I a f M n =
      coefficientAction I f M (monomialCoefficient I a d) ≫
        eqToHom (congrArg
          (fun k ↦
            (idealPowerProductSubobject
              ((Scheme.idealSheafDataOfIdealOnSpec I).comap f) M k : X.Modules))
          (Nat.mul_one n).symm) := sorry

/-- Positive exponentiation makes the powered ideal-product filtration a subfiltration of the
ordinary ideal-product filtration. -/
theorem powered_le {X : Scheme.{u}} (J : X.IdealSheafData) (M : X.Modules)
    {c : ℕ} (hc : 1 ≤ c) (n : ℕ) :
    idealPowerProductSubobject J M (n * c) ≤
      idealPowerProductSubobject J M (n * 1) := sorry

/-- The canonical degreewise inclusion from the `c`-powered Rees-module sheaf to the ordinary
Rees-module sheaf. -/
noncomputable def powerInclusion {X : Scheme.{u}} (J : X.IdealSheafData)
    (M : X.Modules) {c : ℕ} (hc : 1 ≤ c) : powered J M c ⟶ powered J M 1 :=
  fun n ↦ Subobject.ofLE _ _ (powered_le J M hc n)

/-- Each component of the power inclusion followed by the ambient subobject arrow is the
source ideal-power inclusion. -/
theorem powerInclusion_app_arrow {X : Scheme.{u}} (J : X.IdealSheafData)
    (M : X.Modules) {c : ℕ} (hc : 1 ≤ c) (n : ℕ) :
    powerInclusion J M hc n ≫ (idealPowerProductSubobject J M (n * 1)).arrow =
      (idealPowerProductSubobject J M (n * c)).arrow := sorry

/-- The value of a graded algebra map on a degree-`n` powered coefficient is homogeneous of
degree `n`. -/
theorem polynomialLift_mem_grade {A : Type u} [CommRing A] [IsNoetherianRing A]
    {r c n : ℕ} (I : Ideal A)
    (Φ : ReesAlgebra.Grading.grade (I ^ c) →ₐᵍ[A]
      MvPolynomial.standardGrading (Fin r) A)
    (g : (I ^ (n * c) : Ideal A)) :
    Φ (ReesAlgebra.Grading.linear (I ^ c) n
      (Ideal.ReesModule.powerCoefficient I g)) ∈
        MvPolynomial.standardGrading (Fin r) A n := sorry

/-- A graded sheaf map has the coefficientwise formula induced by the graded algebra map `Φ`. -/
def IsPolynomialLift {A : Type u} [CommRing A] [IsNoetherianRing A]
    {r c : ℕ} (I : Ideal A) {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (M : X.Modules)
    (Φ : ReesAlgebra.Grading.grade (I ^ c) →ₐᵍ[A]
      MvPolynomial.standardGrading (Fin r) A)
    (Ψ : powered ((Scheme.idealSheafDataOfIdealOnSpec I).comap f) M c ⟶
      polynomial r M) : Prop :=
  ∀ (n : ℕ) (g : (I ^ (n * c) : Ideal A)),
    coefficientAction I f M g ≫ Ψ n =
      homogeneousAction f M
        ⟨Φ (ReesAlgebra.Grading.linear (I ^ c) n
            (Ideal.ReesModule.powerCoefficient I g)),
          polynomialLift_mem_grade I Φ g⟩

/-- The polynomial-lift predicate is exactly its coefficientwise homogeneous formula. -/
theorem isPolynomialLift_iff {A : Type u} [CommRing A] [IsNoetherianRing A]
    {r c : ℕ} (I : Ideal A) {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (M : X.Modules)
    (Φ : ReesAlgebra.Grading.grade (I ^ c) →ₐᵍ[A]
      MvPolynomial.standardGrading (Fin r) A)
    (Ψ : powered ((Scheme.idealSheafDataOfIdealOnSpec I).comap f) M c ⟶
      polynomial r M) :
    IsPolynomialLift I f M Φ Ψ ↔
      ∀ (n : ℕ) (g : (I ^ (n * c) : Ideal A)),
        coefficientAction I f M g ≫ Ψ n =
          homogeneousAction f M
            ⟨Φ (ReesAlgebra.Grading.linear (I ^ c) n
                (Ideal.ReesModule.powerCoefficient I g)),
              polynomialLift_mem_grade I Φ g⟩ := sorry

end AlgebraicGeometry.Scheme.Modules.FormalReesModule

open AlgebraicGeometry.Scheme.CoherentFormalModules
open AlgebraicGeometry.Scheme.Modules

namespace Ideal.LocalCohomology

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- For a coherent formal module on a Noetherian scheme over `Spec A` and an ideal of
cohomological dimension one, increasing the positive exponent and restricting the coefficient
maps yields a unique graded polynomial lift of the inverse-limit sheaf. The lift acts by the
prescribed homogeneous coefficients and composes with evaluation at the generators to the
canonical inclusion into the ordinary Rees-module sheaf. -/
theorem existsUniqueGradedPolynomialFormalLift
    {r : ℕ} (I : Ideal A) (a : Fin r → I)
    (hgen : Ideal.span (Set.range fun j ↦ (a j : A)) = I)
    (hcd : dimension I I.fg_of_isNoetherianRing = 1)
    {c : ℕ} (hc : 1 ≤ c) (φ : Fin r → I.powerHom A c)
    (hφ : ∑ j, (a j : A) • φ j = (I ^ c).subtype)
    {X : Scheme.{u}} [IsNoetherian X]
    (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.CoherentFormalModules
      ((Scheme.idealSheafDataOfIdealOnSpec I).comap f)) :
    ∃ (c' : ℕ) (hcc : c ≤ c') (hc' : 1 ≤ c'),
      ∃ φ' : Fin r → I.powerHom A c',
        (∀ j, φ' j = (φ j).comp
          (Submodule.inclusion (Ideal.pow_le_pow_right hcc))) ∧
        (∑ j, (a j : A) • φ' j = (I ^ c').subtype) ∧
        ∃ Φ : ReesAlgebra.Grading.grade (I ^ c') →ₐᵍ[A]
            MvPolynomial.standardGrading (Fin r) A,
          (∀ g : (I ^ c' : Ideal A),
            Φ (ReesAlgebra.Grading.degreeOne (I ^ c') g) =
              ∑ j, MvPolynomial.C (φ' j g) * MvPolynomial.X j) ∧
          (ReesAlgebra.Presentation.toRees a).comp Φ.toAlgHom =
            (ReesAlgebra.Grading.powerInclusion I hc').toAlgHom ∧
          (∃! Ψ : FormalReesModule.powered
                ((Scheme.idealSheafDataOfIdealOnSpec I).comap f)
                (limitModule F) c' ⟶
              FormalReesModule.polynomial r (limitModule F),
            FormalReesModule.IsPolynomialLift I f (limitModule F) Φ Ψ) ∧
          ∀ Ψ : FormalReesModule.powered
                ((Scheme.idealSheafDataOfIdealOnSpec I).comap f)
                (limitModule F) c' ⟶
              FormalReesModule.polynomial r (limitModule F),
            FormalReesModule.IsPolynomialLift I f (limitModule F) Φ Ψ →
              Ψ ≫ FormalReesModule.evaluation I a f (limitModule F) =
                FormalReesModule.powerInclusion
                  ((Scheme.idealSheafDataOfIdealOnSpec I).comap f)
                  (limitModule F) hc' := sorry


end Ideal.LocalCohomology
