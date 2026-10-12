/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Functor.OfSequence
public import ReasLib.Algebra.IndEtaleEnvelope.Envelope
public import ReasLib.RingTheory.Etale.Retraction
public import ReasLib.RingTheory.RingHom.IndEtale.Basic

/-!
# Sequential iteration of the ind-étale envelope

The iterates of the ind-étale envelope form a sequential diagram of commutative
rings. Its colimit is a faithfully flat ind-étale algebra over the initial ring
such that every faithfully flat étale algebra over it admits a retraction.
Stages are indexed from zero, with `iterate A 0 = IndEtaleEnvelope A`.
-/

@[expose] public section

universe u

open CategoryTheory Limits CommRingCat

namespace Algebra.IndEtaleEnvelope

/-- The iterated envelopes as commutative ring objects, starting with `T(A)`
and taking the envelope of the previous stage at each successor. -/
noncomputable def iterateObj (A : Type u) [CommRing A] : ℕ → CommRingCat.{u}
  | 0 => of (IndEtaleEnvelope A)
  | n + 1 => of (IndEtaleEnvelope (iterateObj A n : Type u))

/-- The iterates `T^{n+1}(A)`, indexed so that `iterate A 0` is `T(A)`. -/
noncomputable def iterate (A : Type u) [CommRing A] (n : ℕ) : Type u :=
  iterateObj A n

/-- The commutative ring structure on each iterate `T^{n+1}(A)`. -/
noncomputable instance instCommRing_iterate (A : Type u) [CommRing A] (n : ℕ) :
    CommRing (iterate A n) :=
  inferInstanceAs (CommRing (iterateObj A n))

/-- The successor algebra structure `T^{n+1}(A) → T^{n+2}(A)`. -/
noncomputable instance instAlgebra_succ (A : Type u) [CommRing A] (n : ℕ) :
    Algebra (iterate A n) (iterate A (n + 1)) :=
  inferInstanceAs (Algebra (iterate A n) (IndEtaleEnvelope (iterate A n)))

/-- The zeroth iterate is the envelope `T(A)`. -/
theorem iterate_zero (A : Type u) [CommRing A] :
    iterate A 0 = IndEtaleEnvelope A := sorry

/-- The successor iterate is the envelope of the previous stage. -/
theorem iterate_succ (A : Type u) [CommRing A] (n : ℕ) :
    iterate A (n + 1) = IndEtaleEnvelope (iterate A n) := sorry

/-- The `n`-th iterate as a commutative ring object is `of (iterate A n)`. -/
theorem iterateObj_eq_of (A : Type u) [CommRing A] (n : ℕ) :
    iterateObj A n = of (iterate A n) := sorry

/-- The successor morphism of the iterated envelope system. -/
noncomputable def succHom (A : Type u) [CommRing A] (n : ℕ) :
    iterateObj A n ⟶ iterateObj A (n + 1) :=
  ofHom (algebraMap (iterate A n) (iterate A (n + 1)))

/-- The successor morphism is the structure map of the next envelope. -/
theorem succHom_hom (A : Type u) [CommRing A] (n : ℕ) :
    (succHom A n).hom = algebraMap (iterate A n) (iterate A (n + 1)) := sorry

/-- The `ℕ`-indexed diagram of iterated envelopes. -/
noncomputable def iterateFunctor (A : Type u) [CommRing A] : ℕ ⥤ CommRingCat.{u} :=
  Functor.ofSequence (succHom A)

/-- The sequential diagram evaluates at `n` to the `n`-th iterate. -/
theorem iterateFunctor_obj (A : Type u) [CommRing A] (n : ℕ) :
    (iterateFunctor A).obj n = iterateObj A n := sorry

/-- The sequential colimit of the iterated envelopes `T^{n+1}(A)`. -/
noncomputable def Iteration (A : Type u) [CommRing A] : Type u :=
  (colimit (iterateFunctor A) : CommRingCat.{u})

/-- The colimit ring structure on `Iteration A`. -/
noncomputable instance instCommRing_iteration (A : Type u) [CommRing A] :
    CommRing (Iteration A) :=
  inferInstanceAs (CommRing (colimit (iterateFunctor A) : CommRingCat.{u}))

/-- Coprojections from the iterates into the sequential colimit. -/
noncomputable def ι (A : Type u) [CommRing A] (n : ℕ) :
    iterate A n →+* Iteration A :=
  (colimit.ι (iterateFunctor A) n).hom

/-- Each iterate maps to the sequential colimit as an algebra. -/
noncomputable instance instAlgebra_ι (A : Type u) [CommRing A] (n : ℕ) :
    Algebra (iterate A n) (Iteration A) :=
  RingHom.toAlgebra (ι A n)

/-- Coprojections of `Iteration A` intertwine the successor algebra maps. -/
theorem ι_comp_succHom (A : Type u) [CommRing A] (n : ℕ) :
    (ι A (n + 1)).comp (succHom A n).hom = ι A n := sorry

/-- The structure map `A → Iteration A` through the envelope `T(A)`. -/
noncomputable def algebraMap_iteration (A : Type u) [CommRing A] :
    A →+* Iteration A :=
  (colimit.ι (iterateFunctor A) 0).hom.comp (algebraMap_self A)

/-- `Iteration A` is an `A`-algebra via the coprojection through `T(A)`. -/
noncomputable instance instAlgebra_iteration (A : Type u) [CommRing A] :
    Algebra A (Iteration A) :=
  RingHom.toAlgebra (algebraMap_iteration A)

/-- The `A`-algebra structure map of `Iteration A` factors through `T(A)`. -/
theorem algebraMap_iteration_eq (A : Type u) [CommRing A] :
    algebraMap A (Iteration A) = algebraMap_iteration A := sorry

/-- The sequential colimit of the iterated envelopes is faithfully flat
over the initial ring. -/
instance instFaithfullyFlat (A : Type u) [CommRing A] :
    Module.FaithfullyFlat A (Iteration A) := sorry

/-- The sequential colimit of the iterated envelopes is ind-étale
over the initial ring. -/
theorem indEtale (A : Type u) [CommRing A] :
    (algebraMap A (Iteration A)).IndEtale := sorry

/-- Every faithfully flat étale algebra over the sequential colimit of the
iterated envelopes admits a retraction. -/
instance instHasFaithfullyFlatEtaleRetraction (A : Type u) [CommRing A] :
    HasFaithfullyFlatEtaleRetraction (Iteration A) := sorry

/-- The sequential colimit of the iterated envelopes is a faithfully flat
ind-étale algebra with the faithfully flat étale retraction property. -/
theorem iteration_spec (A : Type u) [CommRing A] :
    Module.FaithfullyFlat A (Iteration A) ∧
      (algebraMap A (Iteration A)).IndEtale ∧
      HasFaithfullyFlatEtaleRetraction (Iteration A) := sorry

/-- Every commutative ring admits a faithfully flat ind-étale algebra over
which every faithfully flat étale algebra admits a retraction. -/
theorem exists_faithfullyFlat_indEtale_retraction (A : Type u) [CommRing A] :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C),
      Module.FaithfullyFlat A C ∧ (algebraMap A C).IndEtale ∧
      HasFaithfullyFlatEtaleRetraction C := sorry

end Algebra.IndEtaleEnvelope
