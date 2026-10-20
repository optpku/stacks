module

public import ReasLib.AlgebraicGeometry.Scheme.ProjectiveLineFamily.Moving
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 43.24.2: if closed subvarieties `C` and `X` of `ℙ(V)` intersect
properly and `T i` is a finite collection of closed subvarieties of `X`, then
there is a closed integral family over `ℙ¹` with zero fiber `C`, intersecting
`X × ℙ¹` properly, whose infinity fiber intersects every `T i` properly. -/
@[stacks 0B1T] #check
  (AlgebraicGeometry.ProjectiveLineFamily.existsMovingSubvariety :
    ∀ {k : Type u} [Field k] [IsAlgClosed k]
      {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
      [Nontrivial V]
      {I : Type u} [Finite I]
      (N : ℕ) (hV : Module.finrank k V = N + 1)
      (X : AlgebraicGeometry.SchemeOverField k) [AlgebraicGeometry.Variety X]
      (iX : X ⟶ CategoryTheory.Over.mk
        (AlgebraicGeometry.ProjectiveSpace.VectorSpace.toSpec k V))
      [AlgebraicGeometry.IsClosedImmersion iX.left]
      (C : (AlgebraicGeometry.ProjectiveSpace.VectorSpace.scheme k V).IdealSheafData)
      [AlgebraicGeometry.Variety (CategoryTheory.Over.mk
        (C.subschemeι ≫ AlgebraicGeometry.ProjectiveSpace.VectorSpace.toSpec k V))]
      (T : I → X.left.IdealSheafData)
      [∀ i, AlgebraicGeometry.Variety (CategoryTheory.Over.mk
        ((T i).subschemeι ≫ X.hom))]
      (hproper : TopologicalSpace.Closeds.IntersectProperly C.support
        (iX.left.ker).support),
      ∃ C' : (AlgebraicGeometry.ProjectiveLineFamily.space (CategoryTheory.Over.mk
          (AlgebraicGeometry.ProjectiveSpace.VectorSpace.toSpec k V))).IdealSheafData,
        AlgebraicGeometry.Variety (CategoryTheory.Over.mk
          (C'.subschemeι ≫
            CategoryTheory.Limits.pullback.fst
              (AlgebraicGeometry.ProjectiveSpace.VectorSpace.toSpec k V)
              (AlgebraicGeometry.ProjectiveSpace.toBase 1
                (AlgebraicGeometry.Spec (CommRingCat.of k))) ≫
            AlgebraicGeometry.ProjectiveSpace.VectorSpace.toSpec k V)) ∧
        AlgebraicGeometry.IsDominant
          (C'.subschemeι ≫
            CategoryTheory.Limits.pullback.snd
              (AlgebraicGeometry.ProjectiveSpace.VectorSpace.toSpec k V)
              (AlgebraicGeometry.ProjectiveSpace.toBase 1
                (AlgebraicGeometry.Spec (CommRingCat.of k)))) ∧
        AlgebraicGeometry.ProjectiveLineFamily.zeroImage
            (CategoryTheory.Over.mk
              (AlgebraicGeometry.ProjectiveSpace.VectorSpace.toSpec k V)) C' = C ∧
        TopologicalSpace.Closeds.IntersectProperly C'.support
          (((iX.left.ker).comap
            (CategoryTheory.Limits.pullback.fst
              (AlgebraicGeometry.ProjectiveSpace.VectorSpace.toSpec k V)
              (AlgebraicGeometry.ProjectiveSpace.toBase 1
                (AlgebraicGeometry.Spec (CommRingCat.of k))))).support) ∧
        ∀ i, TopologicalSpace.Closeds.IntersectProperly
          (AlgebraicGeometry.ProjectiveLineFamily.infinityImage
            (CategoryTheory.Over.mk
              (AlgebraicGeometry.ProjectiveSpace.VectorSpace.toSpec k V)) C').support
          ((T i).map iX.left).support)
