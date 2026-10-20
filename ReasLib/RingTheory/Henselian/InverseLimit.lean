module

public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.RingTheory.Henselian
public import ReasLib.Algebra.Category.CommRingCat.InverseSystem
import Mathlib.Tactic.CrossRefAttribute

/-!
# Inverse limits of henselian pairs

Compatible inverse systems of henselian pairs remain henselian after taking the categorical
inverse limit of their underlying commutative rings.  For sequential systems, surjective
successor maps with locally nilpotent kernels also make each limit-projection kernel henselian.

@stack 0EM6
@stack 0CT7
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CategoryTheory.SequentialInverseSystem

/-- Every long transition map has locally nilpotent kernel when this holds for every successor
transition.

The hypothesis uses the system-level `KernelLocallyNilpotent` predicate, while the indices and
their order proof remain explicit selected data. -/
@[stacks 0CT7 "locally nilpotent kernels of long transition maps"]
theorem transitionMap_ker_isLocallyNilpotent
    (F : SequentialInverseSystem CommRingCat.{u})
    (h_locnil : F.KernelLocallyNilpotent) {n m : ℕ} (hnm : n ≤ m) :
    (RingHom.ker (F.transitionMap hnm).hom).IsLocallyNilpotent := sorry

/-- A limit projection of a surjective sequential inverse system with locally nilpotent
successor kernels defines a henselian pair.

This is a theorem rather than an instance because the selected stage and the two stagewise
proofs are not determined by the resulting ring and ideal. -/
@[stacks 0CT7 "henselian kernel of a sequential limit projection"]
theorem limitProjection_ker_henselianRing
    (F : SequentialInverseSystem CommRingCat.{u}) (n : ℕ)
    (h_surj : F.Surjective) (h_locnil : F.KernelLocallyNilpotent) :
    HenselianRing ((limit F : CommRingCat.{u}) : Type u)
      (RingHom.ker (limit.π F (Opposite.op n)).hom) := sorry

end CategoryTheory.SequentialInverseSystem

namespace HenselianRing

/-- Lemma 15.11.12, Stacks `0EM6`: the inverse limit of a compatible inverse system of henselian
pairs is henselian for the ideal obtained by intersecting the inverse images of the stage
ideals. -/
@[stacks 0EM6 "inverse limit of henselian pairs"]
theorem inverseLimit
    {J : Type v} [Preorder J] (F : Jᵒᵖ ⥤ CommRingCat.{u})
    (I : ∀ j : Jᵒᵖ, Ideal (F.obj j)) [UnivLE.{v, u}]
    (hI : ∀ ⦃j k : Jᵒᵖ⦄ (f : j ⟶ k), Ideal.map (F.map f).hom (I j) ≤ I k)
    [∀ j, HenselianRing (F.obj j) (I j)] :
    HenselianRing ((limit F : CommRingCat.{u}) : Type u)
      (⨅ j, Ideal.comap ((limit.π F j).hom) (I j)) := sorry

end HenselianRing
