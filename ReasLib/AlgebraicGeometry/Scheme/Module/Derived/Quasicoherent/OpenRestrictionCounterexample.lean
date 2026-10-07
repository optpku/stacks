module

public import ReasLib.Algebra.Category.ModuleCat.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Adjunction
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.BaseChange.RightAdjoint
public import ReasLib.CategoryTheory.DerivedCategory.Limit.CountableCoproduct
public import ReasLib.RingTheory.DualNumber.Finiteness
public import ReasLib.RingTheory.DualNumber.Residue
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.Algebra.Category.ModuleCat.AB

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped DualNumber

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- The polynomial ring over a field and its dual-number extension are both Noetherian affine
schemes. -/
theorem dualNumberPolynomialSpectra_noetherian (k : Type u) [Field k] :
    let R := Polynomial k
    let A := R[ε]
    IsNoetherian (Spec (CommRingCat.of R)) ∧
      IsNoetherian (Spec (CommRingCat.of A)) := sorry

/-- Reduction from the dual-number extension to the polynomial ring induces a finite affine
scheme morphism. -/
theorem dualNumberPolynomialResidue_isFinite (k : Type u) [Field k] :
    let R := Polynomial k
    let A := R[ε]
    let φ : CommRingCat.of A ⟶ CommRingCat.of R :=
      CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom
    IsFinite (Spec.map φ) := sorry

/-- The indexed coproduct of shifted residue modules has finitely presented cohomology over the
dual-number polynomial ring. -/
theorem dualNumberPolynomialCoproduct_coherent (k : Type u) [Field k] :
    let R := Polynomial k
    let A := R[ε]
    let M : ℕ → ModuleCat A := fun n ↦
      ModuleCat.of A
        (A ⧸ (DualNumber.epsIdeal R ⊔
          Ideal.span {TrivSqZeroExt.inl ((Polynomial.X : R) ^ (n + 1))}))
    let K₀ : DerivedCategory.{u + 1} (ModuleCat A) :=
      ∐ fun n : ℕ ↦
        ((DerivedCategory.singleFunctor (ModuleCat.{u, u} A) 0).obj (M n))
          ⟦((n + 1 : ℕ) : ℤ)⟧
    DerivedCategory.cohomologyIn (ModuleCat.isFinitePresentation A) K₀ := sorry

/-- The principal open defined by the polynomial variable in the dual-number polynomial spectrum
is compact. -/
instance dualNumberPolynomialBasicOpenCompactSpace (k : Type u) [Field k] :
    let R := Polynomial k
    let A := CommRingCat.of R[ε]
    let Y := Spec A
    let V : Y.Opens :=
      PrimeSpectrum.basicOpen (TrivSqZeroExt.inl (Polynomial.X : R))
    CompactSpace V := sorry

/-- The inverse image of that principal open under the residue morphism is compact. -/
instance dualNumberPolynomialPreimageBasicOpenCompactSpace
    (k : Type u) [Field k] :
    let R := Polynomial k
    let A := CommRingCat.of R[ε]
    let φ : A ⟶ CommRingCat.of R :=
      CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom
    let Y := Spec A
    let X := Spec (CommRingCat.of R)
    let f : X ⟶ Y := Spec.map φ
    let V : Y.Opens :=
      PrimeSpectrum.basicOpen (TrivSqZeroExt.inl (Polynomial.X : R))
    CompactSpace (f ⁻¹ᵁ V) := sorry

/-- The principal open defined by the polynomial variable in the dual-number polynomial spectrum
is quasi-separated. -/
instance dualNumberPolynomialBasicOpenQuasiSeparatedSpace
    (k : Type u) [Field k] :
    let R := Polynomial k
    let A := CommRingCat.of R[ε]
    let Y := Spec A
    let V : Y.Opens :=
      PrimeSpectrum.basicOpen (TrivSqZeroExt.inl (Polynomial.X : R))
    QuasiSeparatedSpace V := sorry

/-- The inverse image of that principal open under the residue morphism is quasi-separated. -/
instance dualNumberPolynomialPreimageBasicOpenQuasiSeparatedSpace
    (k : Type u) [Field k] :
    let R := Polynomial k
    let A := CommRingCat.of R[ε]
    let φ : A ⟶ CommRingCat.of R :=
      CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom
    let Y := Spec A
    let X := Spec (CommRingCat.of R)
    let f : X ⟶ Y := Spec.map φ
    let V : Y.Opens :=
      PrimeSpectrum.basicOpen (TrivSqZeroExt.inl (Polynomial.X : R))
    QuasiSeparatedSpace (f ⁻¹ᵁ V) := sorry

/-- For the residue morphism of the dual-number polynomial extension, the derived
open-restriction right-adjoint comparison fails to be invertible on the shifted coproduct of
residue modules. -/
theorem dualNumberPolynomial_openRestrictionComparison_not_isIso
    (k : Type u) [Field k] :
    let R := Polynomial k
    let A := CommRingCat.of R[ε]
    let φ : A ⟶ CommRingCat.of R :=
      CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom
    let Y := Spec A
    let X := Spec (CommRingCat.of R)
    let f : X ⟶ Y := Spec.map φ
    let V : Y.Opens :=
      PrimeSpectrum.basicOpen (TrivSqZeroExt.inl (Polynomial.X : R))
    let U : X.Opens := f ⁻¹ᵁ V
    let M : ℕ → ModuleCat A := fun n ↦
      ModuleCat.of A
        (A ⧸ (DualNumber.epsIdeal R ⊔
          Ideal.span {TrivSqZeroExt.inl ((Polynomial.X : R) ^ (n + 1))}))
    let K₀ : DerivedCategory.{u + 1} (ModuleCat A) :=
      ∐ fun n : ℕ ↦
        ((DerivedCategory.singleFunctor (ModuleCat.{u, u} A) 0).obj (M n))
          ⟦((n + 1 : ℕ) : ℤ)⟧
    let K : DerivedQCoh Y :=
      (@Functor.inv _ _ _ _ (affineGlobalSections A)
        (affineGlobalSectionsIsEquivalence A)).obj K₀
    ∀ (a : DerivedQCoh Y ⥤ DerivedQCoh X)
      (aV : DerivedQCoh V.toScheme ⥤ DerivedQCoh U.toScheme)
      (aAdjunction : pushforwardCohomologyIn f ⊣ a)
      (aVAdjunction : pushforwardCohomologyIn (f ∣_ V) ⊣ aV),
      ¬ IsIso
        ((DerivedBaseChange.mapOfRight
          (pullbackPushforwardAdjunction V.ι)
          (pullbackPushforwardAdjunction U.ι)
          (@asIso _ _ _ _
            (BaseChange.rightMate U.ι (f ∣_ V) f V.ι
              (isPullback_morphismRestrict f V).flip.toCommSq
              a aV aAdjunction aVAdjunction)
            (BaseChange.rightMate_isIso_of_flat
              U.ι (f ∣_ V) f V.ι
              (isPullback_morphismRestrict f V).flip
              a aV aAdjunction aVAdjunction)).inv).app K) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
