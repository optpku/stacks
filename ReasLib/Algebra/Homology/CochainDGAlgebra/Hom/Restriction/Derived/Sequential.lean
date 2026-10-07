module

public import ReasLib.Algebra.Homology.CochainDGAlgebra.Hom.Restriction.Derived.Coherence
public import ReasLib.CategoryTheory.InverseSystem.Sequential
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived restriction along a sequential DGA system

The identity and composition coherence of derived restriction specialize canonically to the
transition maps of a sequential inverse system of cochain DGAs.
-/

@[expose] public section

noncomputable section

universe u x v

open CategoryTheory Opposite

namespace CochainDGAlgebra.InverseSystem.Derived

variable {R : Type u} [CommRing R]

/-- Derived restriction along a reflexive transition is canonically the identity functor. -/
@[stacks 0GZI "identity coherence for derived restriction along a DGA system"]
noncomputable def restrictionReflIso
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R)) (i : ℕ) :
    𝟭 (DifferentialGradedModule.Derived.Category.{u, v} (A.obj (op i))) ≅
      CochainDGAlgebra.Hom.Derived.restriction
        (A.transitionMap (le_refl i)) :=
  CochainDGAlgebra.Hom.Derived.restrictionIdIso (A.obj (op i)) ≪≫
    eqToIso (congrArg CochainDGAlgebra.Hom.Derived.restriction
      (A.transitionMap_refl i).symm)

/-- Successive derived restrictions along DGA transitions are canonically identified with
restriction along the composite transition. -/
@[stacks 0GZI "composition coherence for derived restriction along a DGA system"]
noncomputable def restrictionCompIso
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R))
    {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    CochainDGAlgebra.Hom.Derived.restriction (A.transitionMap hij) ⋙
        CochainDGAlgebra.Hom.Derived.restriction (A.transitionMap hjk) ≅
      CochainDGAlgebra.Hom.Derived.restriction
        (A.transitionMap (Nat.le_trans hij hjk)) :=
  CochainDGAlgebra.Hom.Derived.restrictionCompIso
      (A.transitionMap hjk) (A.transitionMap hij) ≪≫
    eqToIso (congrArg CochainDGAlgebra.Hom.Derived.restriction
      (A.transitionMap_comp hij hjk).symm)

/-- Derived extension along a reflexive transition is canonically the identity functor. -/
@[stacks 0GZI "identity coherence for derived extension along a DGA system"]
noncomputable def extensionReflIso
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R)) (i : ℕ) :
    CochainDGAlgebra.Hom.Derived.extension.{u, x}
        (A.transitionMap (le_refl i)) ≅
      𝟭 (DifferentialGradedModule.Derived.Category.{u, x} (A.obj (op i))) :=
  eqToIso (congrArg CochainDGAlgebra.Hom.Derived.extension.{u, x}
      (A.transitionMap_refl i)) ≪≫
    CochainDGAlgebra.Hom.Derived.extensionIdIso.{u, x} (A.obj (op i))

/-- Successive derived extensions along DGA transitions are canonically identified with
extension along the composite transition. -/
@[stacks 0GZI "composition coherence for derived extension along a DGA system"]
noncomputable def extensionCompIso
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R))
    {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    CochainDGAlgebra.Hom.Derived.extension.{u, x} (A.transitionMap hjk) ⋙
        CochainDGAlgebra.Hom.Derived.extension.{u, x} (A.transitionMap hij) ≅
      CochainDGAlgebra.Hom.Derived.extension.{u, x}
        (A.transitionMap (Nat.le_trans hij hjk)) :=
  CochainDGAlgebra.Hom.Derived.extensionCompIso.{u, x}
      (A.transitionMap hjk) (A.transitionMap hij) ≪≫
    eqToIso (congrArg CochainDGAlgebra.Hom.Derived.extension.{u, x}
      (A.transitionMap_comp hij hjk).symm)

end CochainDGAlgebra.InverseSystem.Derived
