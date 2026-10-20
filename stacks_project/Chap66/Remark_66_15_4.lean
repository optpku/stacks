module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PointLike.Decent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Decent.Singleton
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Decent.LocallySeparated
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

/- Remark 66.15.4 (1): Lemma 66.15.3 holds for decent algebraic spaces via
Decent Spaces, Lemma 68.12.8. -/
@[stacks 03E0] #check
  (AlgebraicGeometry.AlgebraicSpace.exists_iso_spec_of_surjective_etale :
    ∀ {S : Scheme.{u}} {k : Type u} [Field k]
      {σ : Spec (.of k) ⟶ S} {X : AlgebraicSpace S} (f : ofOver (Over.mk σ) ⟶ X)
      [Etale f] (hf : Function.Surjective (Points.map f)) [IsDecent X],
      ∃ (k' : Type u) (_ : Field k') (_ : Algebra k' k) (σ' : Spec (.of k') ⟶ S)
        (e : X ≅ ofOver (Over.mk σ'))
        (hσ : Spec.map (CommRingCat.ofHom (algebraMap k' k)) ≫ σ' = σ),
        FiniteDimensional k' k ∧ Algebra.IsSeparable k' k ∧
          f ≫ e.hom =
            ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap k' k))) hσ)

/- Remark 66.15.4 (2): a decent algebraic space with one point is a scheme. -/
@[stacks 03E0] #check
  (AlgebraicGeometry.AlgebraicSpace.IsScheme.of_singleton_points :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
      [IsDecent X] [Nonempty (Points X)] [Subsingleton (Points X)],
      IsScheme X)

/- Remark 66.15.4 (3): the preceding conclusions also apply when X is locally
separated because such an X is decent. -/
@[stacks 03E0] #check
  (AlgebraicGeometry.AlgebraicSpace.instIsDecent_of_isAbsolutelyLocallySeparated :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
      [IsAbsolutelyLocallySeparated X], IsDecent X)
