module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.LinearSystem.Separation
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/- Lemma 33.23.1 (1): point and tangent-vector separation by a subspace of global sections of an
invertible module on a proper scheme over an algebraically closed field implies relative very
ampleness. -/
@[stacks 0E8S] #check
  (AlgebraicGeometry.ProjectiveSpace.VectorSpace.LinearSystem.relativelyVeryAmple_of_separatesClosedPoints_and_separatesTangentVectors :
    ∀ {k : Type u} [Field k] [IsAlgClosed k]
      (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom]
      (L : X.left.Modules) [Scheme.Modules.Invertible L]
      (W : Submodule k (Scheme.Hom.globalSectionsMod X.hom L)),
      AlgebraicGeometry.ProjectiveSpace.VectorSpace.LinearSystem.SeparatesClosedPoints X L
          (ConcreteCategory.ofHom (C := ModuleCat k) W.subtype) →
        AlgebraicGeometry.ProjectiveSpace.VectorSpace.LinearSystem.SeparatesTangentVectors X L
            (ConcreteCategory.ofHom (C := ModuleCat k) W.subtype) →
          RelativelyVeryAmple X.hom L)

/- Lemma 33.23.1, proof step: separation of closed points implies that the subspace generates the
module. The source proof asserts this without restriction; it requires at least two closed points
(for `X = Spec k` and `V = 0` both hypotheses hold vacuously but `V` does not generate). -/
@[stacks 0E8S] #check
  (AlgebraicGeometry.ProjectiveSpace.VectorSpace.LinearSystem.generates_of_separatesClosedPoints :
    ∀ {k : Type u} [Field k] {V : Type u} [AddCommGroup V] [Module k V]
      (X : Over (Spec (CommRingCat.of k))) [LocallyOfFiniteType X.hom]
      (L : X.left.Modules) [Scheme.Modules.Invertible L]
      (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L),
      (closedPoints X.left).Nontrivial →
        AlgebraicGeometry.ProjectiveSpace.VectorSpace.LinearSystem.SeparatesClosedPoints X L ψ →
          AlgebraicGeometry.ProjectiveSpace.VectorSpace.LinearSystem.Generates X L ψ)

/- Lemma 33.23.1 (2): for a generating subspace satisfying the separation hypotheses, its
canonical morphism to the projective scheme of that subspace is a closed immersion. Generation is
an explicit premise because of the one-closed-point gap noted above; with at least two closed
points it is supplied by `generates_of_separatesClosedPoints`. -/
@[stacks 0E8S] #check
  (AlgebraicGeometry.ProjectiveSpace.VectorSpace.LinearSystem.inducesClosedImmersion_of_separates :
    ∀ {k : Type u} [Field k] [IsAlgClosed k]
      (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom]
      (L : X.left.Modules) [Scheme.Modules.Invertible L]
      (W : Submodule k (Scheme.Hom.globalSectionsMod X.hom L)),
      AlgebraicGeometry.ProjectiveSpace.VectorSpace.LinearSystem.Generates X L
          (ConcreteCategory.ofHom (C := ModuleCat k) W.subtype) →
      AlgebraicGeometry.ProjectiveSpace.VectorSpace.LinearSystem.SeparatesClosedPoints X L
          (ConcreteCategory.ofHom (C := ModuleCat k) W.subtype) →
        AlgebraicGeometry.ProjectiveSpace.VectorSpace.LinearSystem.SeparatesTangentVectors X L
            (ConcreteCategory.ofHom (C := ModuleCat k) W.subtype) →
          AlgebraicGeometry.ProjectiveSpace.VectorSpace.LinearSystem.InducesClosedImmersion X L
            (ConcreteCategory.ofHom (C := ModuleCat k) W.subtype))
