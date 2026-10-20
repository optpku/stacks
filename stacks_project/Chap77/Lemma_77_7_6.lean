module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.BaseChange.Adjunction
import StacksCheckRecall

/-!
# Lemma 77.7.6

In Situation 77.7.1, an affine morphism `i : Z ⟶ X` with `𝒢 = i_* ℋ` identifies the
vanishing flattening functors of `u` and of its adjoint `v`; if `i` is a closed
immersion, the same holds for the surjectivity functors.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

noncomputable section

universe u

open AlgebraicGeometry.AlgebraicSpace.Modules

/- Lemma 77.7.6. Affine pushforward identifies the vanishing predicates of a morphism
and its canonical adjoint on every scheme over the base. -/
@[stacks 0CW7] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.baseChangeMap_zero_iff_adjoint :
    ∀ {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X)
      {ℱ : X.Modules} {ℋ : Z.Modules} {B : AlgebraicSpace S} (f : X ⟶ B)
      [ℱ.IsQuasicoherent] [ℋ.IsQuasicoherent] (u : ℱ ⟶ (pushforward i).obj ℋ)
      [Affine i] (T : SchemeOver B),
      baseChangeMap f T.hom u = 0 ↔
        baseChangeMap (i ≫ f) T.hom (adjointToPushforward i u) = 0)

#check
  (AlgebraicGeometry.AlgebraicSpace.Modules.baseChangeMap_epi_iff_adjoint :
    ∀ {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X)
      {ℱ : X.Modules} {ℋ : Z.Modules} {B : AlgebraicSpace S} (f : X ⟶ B)
      [ℱ.IsQuasicoherent] [ℋ.IsQuasicoherent] (u : ℱ ⟶ (pushforward i).obj ℋ)
      [IsClosedImmersion i] (T : SchemeOver B),
      Epi (baseChangeMap f T.hom u) ↔
        Epi (baseChangeMap (i ≫ f) T.hom (adjointToPushforward i u)))
