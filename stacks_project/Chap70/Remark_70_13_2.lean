module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AffineSpace.Immersion
import StacksCheckRecall

/-!
# Failure of embedding into affine space without local separatedness

Lemma 70.13.1 needs both quasi-separatedness and local separatedness of the
target. Dropping local separatedness already fails for quasi-separated targets;
whether local separatedness alone suffices is open.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

#check (AlgebraicGeometry.AlgebraicSpace.existsImmersionToAffineSpace :
  {S : Scheme.{u}} → {X U : AlgebraicSpace S} → (U ⟶ X) → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.existsImmersionToAffineSpace_iff :
  ∀ {S : Scheme.{u}} {X U : AlgebraicSpace S} (f : U ⟶ X),
    existsImmersionToAffineSpace f ↔
      ∃ (n : ℕ) (i : U ⟶ AffineSpace (ULift.{u} (Fin n)) X),
        IsImmersion i ∧ i ≫ AffineSpace.toBase (ULift.{u} (Fin n)) X = f)

/- Remark 70.13.2: Dropping local separatedness gives a counterexample even
with a quasi-separated target. Whether local separatedness suffices without
quasi-separatedness remains an open question. -/
@[stacks 088M] #check
  (AlgebraicGeometry.AlgebraicSpace.exists_quasiSeparated_without_immersion_to_affineSpace :
    ∃ (S : Scheme.{u}) (X U : AlgebraicSpace S) (f : U ⟶ X),
      IsAffine U ∧ LocallyOfFiniteType f ∧ IsAbsolutelyQuasiSeparated X ∧
        ¬ existsImmersionToAffineSpace f)

#check (AlgebraicGeometry.AlgebraicSpace.existsImmersionToAffineSpace_of_locallySeparated.{u} :
  Prop)

#check (AlgebraicGeometry.AlgebraicSpace.existsImmersionToAffineSpace_of_locallySeparated_iff.{u} :
  existsImmersionToAffineSpace_of_locallySeparated.{u} ↔
    ∀ {S : Scheme.{u}} {X U : AlgebraicSpace S} (f : U ⟶ X),
      IsAffine U → LocallyOfFiniteType f → IsAbsolutelyLocallySeparated X →
        existsImmersionToAffineSpace f)
