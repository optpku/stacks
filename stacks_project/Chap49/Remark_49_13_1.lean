module

import StacksCheckRecall
import stacks_project.Chap49.Lemma_49_10_1
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.QuasiFinite
import ReasLib.RingTheory.CompleteIntersection.RelativeGlobal.Local
import ReasLib.RingTheory.Extension.Cotangent.Determinant
import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u v

/- Remark 49.13.1 (1): a locally quasi-finite syntomic morphism admits affine
neighborhoods with a square relative-global-complete-intersection presentation. -/
@[stacks 0FKC] #check (AlgebraicGeometry.quasiFiniteSyntomic_tfae :
  ∀ {X Y : Scheme.{u}} (f : Y ⟶ X)
    [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules Y.toRingedSpace)],
    let L : RingedSpace.ModuleDerived Y.toRingedSpace :=
      DerivedCategory.Q.obj (RingedSpace.naiveCotangent f.toShHom)
    List.TFAE [
      LocallyQuasiFinite f ∧ Syntomic f,
      LocallyQuasiFinite f ∧ Flat f ∧
        LocallyOfType RingHom.IsLocalCompleteIntersection f,
      LocallyQuasiFinite f ∧ Flat f ∧ LocallyOfFinitePresentation f ∧
        ∀ x : X, IsLocalCompleteIntersectionOver (X.residueField x)
          (f.fiberToSpecResidueField x),
      LocallyQuasiFinite f ∧
        ∀ y : Y, ∃ V : Y.affineOpens, y ∈ (V : Y.Opens) ∧
          ∃ U : X.affineOpens, ∃ e : V ≤ f ⁻¹ᵁ U,
            ∃ n : ℕ, ∃ h : MvPolynomial (Fin n) Γ(X, U),
              ∃ g : Fin n → MvPolynomial (Fin n) Γ(X, U),
                ∃ q : Localization.Away h →+* Γ(Y, V),
                  Function.Surjective q ∧
                    q.comp (algebraMap Γ(X, U) (Localization.Away h)) =
                      (f.appLE U V e).hom ∧
                    RingHom.ker q = Ideal.span
                      (Set.range fun i ↦
                        algebraMap (MvPolynomial (Fin n) Γ(X, U))
                          (Localization.Away h) (g i)),
      ∀ y : Y, ∃ V : Y.affineOpens, y ∈ (V : Y.Opens) ∧
        ∃ U : X.affineOpens, ∃ e : V ≤ f ⁻¹ᵁ U,
          ∃ n : ℕ,
            ∃ P : @Algebra.Presentation Γ(X, U) Γ(Y, V) (Fin n) (Fin n)
                _ _ (f.appLE U V e).hom.toAlgebra,
              @Algebra.Presentation.IsRelativeGlobalCompleteIntersection
                Γ(X, U) Γ(Y, V) _ _ (f.appLE U V e).hom.toAlgebra n n P,
      LocallyQuasiFinite f ∧ Flat f ∧ LocallyOfFinitePresentation f ∧
        RingedSpace.HasTorAmplitudeIn L (-1) 0,
      Flat f ∧ LocallyOfFinitePresentation f ∧
        RingedSpace.ModuleDerived.IsPerfect L ∧
          Scheme.ModuleDerived.fiberEulerChar L = (fun _ ↦ (0 : ℤ)) ∧
        RingedSpace.HasTorAmplitudeIn L (-1) 0])

/- Remark 49.13.1 (2): on an affine square complete-intersection chart, the naive
cotangent complex is the two-term presentation complex from the conormal module
to the free module on the coordinate differentials. -/
@[stacks 0FKC] #check (Algebra.Extension.NaiveCotangent.complex :
  ∀ {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S],
    Algebra.Extension R S → ChainComplex (ModuleCat S) ℕ)

/- Remark 49.13.1 (3): the classes of the displayed relations form a basis of
the presentation conormal module. -/
@[stacks 0FKC] #check (Algebra.Presentation.IsRelativeGlobalCompleteIntersection.exists_basisCotangent_naive :
  ∀ {R : Type u} [CommRing R] {n c : ℕ}
    {f : Fin c → MvPolynomial (Fin n) R},
    (Algebra.Presentation.naive : Algebra.Presentation R
      (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))
      (Fin n) (Fin c)).IsRelativeGlobalCompleteIntersection →
    ∃ b : Module.Basis (Fin c)
      (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))
      (Ideal.span (Set.range f)).Cotangent,
      ∀ i, b i = Ideal.toCotangent _
        ⟨f i, Ideal.subset_span (Set.mem_range_self i)⟩)

/- Remark 49.13.1 (4): the local coordinate determinant line is free on the
ratio of the coordinate-differential wedge and the relation-class wedge. -/
@[stacks 0FKC] #check (Algebra.Presentation.CotangentDeterminant.generator_uniqueScalar :
  ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    {n : ℕ} (P : Algebra.Presentation A B (Fin n) (Fin n))
    (b : Module.Basis (Fin n) B P.toExtension.Cotangent)
    (φ : (⋀[B]^n P.toExtension.Cotangent) →ₗ[B]
      ⋀[B]^n P.toExtension.CotangentSpace),
    ∃! a : B, φ = a •
      Algebra.Presentation.CotangentDeterminant.generator P b)

/- Remark 49.13.1 (5): in those coordinates, the canonical section is the
Jacobian determinant times the displayed generator. -/
@[stacks 0FKC] #check (Algebra.Presentation.CotangentDeterminant.section_eq_smul_generator :
  ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    {n : ℕ} (P : Algebra.Presentation A B (Fin n) (Fin n))
    (b : Module.Basis (Fin n) B P.toExtension.Cotangent),
    (∀ i, b i = Algebra.Extension.Cotangent.mk
      ⟨P.relation i, P.relation_mem_ker i⟩) →
    Algebra.Presentation.CotangentDeterminant.canonicalSection P =
      Matrix.det (Algebra.Presentation.Jacobian.target P) •
        Algebra.Presentation.CotangentDeterminant.generator P b)
