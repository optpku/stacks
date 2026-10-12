/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

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

/- Lemma 33.23.1 (2): under the same separation hypotheses, the subspace generates the module and
its canonical morphism to the projective scheme of that subspace is a closed immersion. -/
@[stacks 0E8S] #check
  (AlgebraicGeometry.ProjectiveSpace.VectorSpace.LinearSystem.inducesClosedImmersion_of_separates :
    ∀ {k : Type u} [Field k] [IsAlgClosed k]
      (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom]
      (L : X.left.Modules) [Scheme.Modules.Invertible L]
      (W : Submodule k (Scheme.Hom.globalSectionsMod X.hom L)),
      AlgebraicGeometry.ProjectiveSpace.VectorSpace.LinearSystem.SeparatesClosedPoints X L
          (ConcreteCategory.ofHom (C := ModuleCat k) W.subtype) →
        AlgebraicGeometry.ProjectiveSpace.VectorSpace.LinearSystem.SeparatesTangentVectors X L
            (ConcreteCategory.ofHom (C := ModuleCat k) W.subtype) →
          AlgebraicGeometry.ProjectiveSpace.VectorSpace.LinearSystem.InducesClosedImmersion X L
            (ConcreteCategory.ofHom (C := ModuleCat k) W.subtype))
