module

public import ReasLib.AlgebraicGeometry.WeilCohomology.CycleClass.OperationalChow
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

universe u v w x z q

/- Lemma 45.14.2: data (D0), (D1), and (D2') satisfying (A1)-(A4) determine a
unique pullback-compatible graded cycle-class ring homomorphism from canonical
operational Chow cohomology, carrying the canonical Chow Chern character to the
cohomological Chern character. -/
@[stacks 0FIF] #check
  (WeilCohomology.existsUniqueCycleClass :
    ∀ {k : Type u} [Field k] {F : Type v} [Field F] [CharZero F]
      {TateLine : Type x} [AddCommGroup TateLine] [Module F TateLine]
      {V : Type w} [Category.{z} V]
      (scheme : V ⥤ SchemeOverField k) [∀ X, Variety (scheme.obj X)]
      [∀ X, Smooth (scheme.obj X).hom] [∀ X, Projective (scheme.obj X).hom]
      (dimension : V → ℕ) (product : V → V → V)
      (fst : ∀ X Y, product X Y ⟶ X) (snd : ∀ X Y, product X Y ⟶ Y)
      (point : V) (scheme_fullyFaithful : scheme.FullyFaithful)
      (dimension_eq : ∀ X,
        topologicalKrullDim (scheme.obj X).left = (dimension X : WithBot ℕ∞))
      (schemeProduct : ∀ X Y, scheme.obj (product X Y) ≅ scheme.obj X ⨯ scheme.obj Y)
      (scheme_fst : ∀ X Y, scheme.map (fst X Y) =
        (schemeProduct X Y).hom ≫ Limits.prod.fst)
      (scheme_snd : ∀ X Y, scheme.map (snd X Y) =
        (schemeProduct X Y).hom ≫ Limits.prod.snd)
      (schemePoint : scheme.obj point ≅ Over.mk (𝟙 (Spec (CommRingCat.of k))))
      (scheme_essentiallySurjective : ∀ (S : SchemeOverField k)
        [Variety S] [Smooth S.hom] [Projective S.hom],
        ∃ X : V, Nonempty (scheme.obj X ≅ S))
      (H : Vᵒᵖ ⥤ RingCat.{q})
      (Hdiag : ∀ X, ℕ → Submodule ℤ (H.obj (Opposite.op X)))
      [∀ X, GradedAlgebra (Hdiag X)] [∀ X, Algebra ℚ (H.obj (Opposite.op X))]
      [∀ X, Algebra F (H.obj (Opposite.op X))]
      (Hgrade : ∀ X, ℤ × ℤ → Submodule F (H.obj (Opposite.op X)))
      (h_diagonal : ∀ X i (a : H.obj (Opposite.op X)),
        a ∈ Hdiag X i ↔ a ∈ Hgrade X (2 * (i : ℤ), (i : ℤ)))
      (tateLine_rank : Module.finrank F TateLine = 1)
      (tateTwist : ∀ X i j,
        Hgrade X (i, j) ⊗[F] TateLine ≃ₗ[F] Hgrade X (i, j + 1))
      (h_pullback_bigrade : ∀ {X Y : V} (f : X ⟶ Y) (p : ℤ × ℤ)
        (a : Hgrade Y p), H.map f.op a ∈ Hgrade X p)
      (chH : ∀ X, Scheme.VectorBundleK0 (scheme.obj X).left →+*
        PowerSeries (H.obj (Opposite.op X)))
      (chH_coeff_mem : ∀ X (alpha : Scheme.VectorBundleK0 (scheme.obj X).left) i,
        PowerSeries.coeff i (chH X alpha) ∈ Hdiag X i)
      (chH_naturality : ∀ {X Y : V} (f : X ⟶ Y)
        (alpha : Scheme.VectorBundleK0 (scheme.obj Y).left),
        PowerSeries.map (H.map f.op).hom (chH Y alpha) =
          chH X (Scheme.VectorBundleK0.pullback (scheme.map f).left alpha))
      (chowTheory : ∀ X, AlgebraicGeometry.ChernClass.Theory
        (fun _ : Spec (CommRingCat.of k) ↦ 0) (scheme.obj X).hom),
      ∃ gamma : WeilCohomology.OperationalChowCycleClass scheme H Hdiag,
        gamma.FactorsChernCharacter chowTheory chH ∧
          ∀ gamma' : WeilCohomology.OperationalChowCycleClass scheme H Hdiag,
            gamma'.FactorsChernCharacter chowTheory chH → gamma' = gamma)
