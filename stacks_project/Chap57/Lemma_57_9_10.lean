module

public import ReasLib.AlgebraicGeometry.Scheme.FourierMukai.KernelBounds
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpace.ModuleDerived

universe u

namespace AlgebraicGeometry.Scheme.FourierMukai

variable {k : Type u} [Field k]

/- Lemma 57.9.10 (1): the zero-dimensional test bounds imply the two-interval bounds
for every perfect kernel stage. -/
@[stacks 0FZ9] #check (AlgebraicGeometry.Scheme.FourierMukai.kernel_amplitude :
  ∀
    (X Y : SchemeOverField k) (hX : Algebraic X) (hY : Algebraic Y) (m : ℕ)
    (K : ℕ ⥤ @RingedSpace.ModuleDerived.Perfect (pullback X.hom Y.hom).toRingedSpace)
    (hK : ∀ (n : ℕ) (q : ℤ), (m : ℤ) < q →
      IsZero (cohomologySheaf (K.obj n).obj q))
    (hF : ∀ (F : X.left.Modules), F.IsCoherent →
      topologicalKrullDim
          (RingedSpace.moduleSupport (Scheme.Modules.toRingedSpaceObj X.left F)) = 0 →
      (∀ n : ℕ, IsSupportedInIntervals (transform X Y F (K.obj n)) m n) ∧
        (∀ n : ℕ, 2 * m < n →
          ∀ i : ℤ, -(m : ℤ) ≤ i → i ≤ (m : ℤ) →
            IsIso (cohomologySheafMap (transition X Y K F n) i))),
    ∀ n : ℕ, IsSupportedInIntervals (K.obj n).obj m n)

/- Lemma 57.9.10 (2): the zero-dimensional test transition isomorphisms imply
central cohomology isomorphisms for the kernel transitions once `n > 2m`. -/
@[stacks 0FZ9] #check (AlgebraicGeometry.Scheme.FourierMukai.kernel_transition_isIso :
  ∀
    (X Y : SchemeOverField k) (hX : Algebraic X) (hY : Algebraic Y) (m : ℕ)
    (K : ℕ ⥤ @RingedSpace.ModuleDerived.Perfect (pullback X.hom Y.hom).toRingedSpace)
    (hK : ∀ (n : ℕ) (q : ℤ), (m : ℤ) < q →
      IsZero (cohomologySheaf (K.obj n).obj q))
    (hF : ∀ (F : X.left.Modules), F.IsCoherent →
      topologicalKrullDim
          (RingedSpace.moduleSupport (Scheme.Modules.toRingedSpaceObj X.left F)) = 0 →
      (∀ n : ℕ, IsSupportedInIntervals (transform X Y F (K.obj n)) m n) ∧
        (∀ n : ℕ, 2 * m < n →
          ∀ i : ℤ, -(m : ℤ) ≤ i → i ≤ (m : ℤ) →
            IsIso (cohomologySheafMap (transition X Y K F n) i))),
    ∀ n : ℕ, 2 * m < n →
      ∀ i : ℤ, -(m : ℤ) ≤ i → i ≤ (m : ℤ) →
        IsIso (cohomologySheafMap ((K.map (homOfLE (Nat.le_succ n))).hom) i))

/- Lemma 57.9.10 (3): over smooth schemes the perfect kernel stages eventually split
into a fixed central summand and shifted lower summands, compatibly with the transitions. -/
@[stacks 0FZ9] #check (AlgebraicGeometry.Scheme.FourierMukai.eventually_split :
  ∀
    (X Y : SchemeOverField k) (hX : Algebraic X) (hY : Algebraic Y)
    [Smooth X.hom] [Smooth Y.hom] (m : ℕ)
    (K : ℕ ⥤ @RingedSpace.ModuleDerived.Perfect (pullback X.hom Y.hom).toRingedSpace)
    (hK : ∀ (n : ℕ) (q : ℤ), (m : ℤ) < q →
      IsZero (cohomologySheaf (K.obj n).obj q))
    (hF : ∀ (F : X.left.Modules), F.IsCoherent →
      topologicalKrullDim
          (RingedSpace.moduleSupport (Scheme.Modules.toRingedSpaceObj X.left F)) = 0 →
      (∀ n : ℕ, IsSupportedInIntervals (transform X Y F (K.obj n)) m n) ∧
        (∀ n : ℕ, 2 * m < n →
          ∀ i : ℤ, -(m : ℤ) ≤ i → i ≤ (m : ℤ) →
            IsIso (cohomologySheafMap (transition X Y K F n) i))),
    ∃ (Klim : RingedSpace.ModuleDerived (pullback X.hom Y.hom).toRingedSpace),
      IsPerfect Klim ∧
      IsSupportedInCentralInterval Klim m ∧
      ∃ (N : ℕ)
        (C : ℕ → RingedSpace.ModuleDerived (pullback X.hom Y.hom).toRingedSpace),
        (∀ n : ℕ, N ≤ n →
          IsPerfect (C n) ∧
            IsSupportedInLowerInterval (C n) m n) ∧
        ∃ (e : ∀ n : ℕ, N ≤ n →
            ((K.obj n).obj ≅ (Klim ⊞ C n)))
          (c : ∀ n : ℕ, C n ⟶ C (n + 1))
          (u : ∀ n : ℕ, Klim ⟶ Klim),
          (∀ n : ℕ, IsIso (u n)) ∧
          ∀ (n : ℕ) (hn : N ≤ n),
            (e n hn).hom ≫ biprod.map (u n) (c n) =
              (K.map (homOfLE (Nat.le_succ n))).hom ≫
                (e (n + 1) (Nat.le_trans hn (Nat.le_succ n))).hom)

end AlgebraicGeometry.Scheme.FourierMukai
