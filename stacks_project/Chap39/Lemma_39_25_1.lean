module

public import ReasLib.AlgebraicGeometry.Scheme.DescentData.Effectivity.FiniteLocallyFree
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 39.25.1: a descent datum along a surjective finite locally free morphism is
effective if its geometric fibers have at most `d` points and every `d`-tuple in a fiber of
its component is contained in an affine open. -/
@[stacks 0H8K] #check
  (AlgebraicGeometry.Scheme.DescentData.IsEffective.ofFiniteLocallyFree :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [Surjective f] [IsFiniteLocallyFree f]
      (d : ℕ) (_ : 0 < d)
      (_ : ∀ (K : Type u) [Field K] [IsAlgClosed K] (p : Spec (.of K) ⟶ Y),
        Finite (pullback f p : Scheme) ∧ Nat.card (pullback f p : Scheme) ≤ d)
      (D : Scheme.DescentData (fun _ : PUnit.{1} ↦ X) (fun _ ↦ f)),
      (∀ (y : Y) (v : Fin d → ((D.obj PUnit.unit).hom ≫ f).pointsOver y),
        ∃ U : (D.obj PUnit.unit).left.affineOpens,
          Set.range (fun i ↦ (v i : (D.obj PUnit.unit).left)) ⊆
            ((U : (D.obj PUnit.unit).left.Opens) : Set (D.obj PUnit.unit).left)) →
        D.IsEffective)
