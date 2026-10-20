module

public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.BaseChange.Bijective
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.Limit
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Pushout squares for directed ring approximations

This leaf owns the ring-level pushout consequence of bijective stage
base-change.  Module-level tensor equivalences live in
`Approximation.ModuleSystem.Pushout`, so the ring owner can be reused without
importing a module-system specialization.
-/

@[expose] public section

universe u v

noncomputable section

namespace Ring.DirectLimit.Algebra.Approximation.Hom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable {f : R →+* S}

/- The algebra structures below are induced by the displayed ring
homomorphisms.  They are local because no single ambient algebra structure is
canonical when a stage has several comparison maps. -/

/-- A stage square in a directed approximation is a pushout when its ring
base-change map is bijective. -/
@[stacks 00R1 "directed approximation final pushout"]
theorem final_isPushout (A : Hom f) (hbc : A.baseChange_bijective)
    (i : A.index) :
    let _ : Algebra (A.source i) (A.target i) := (A.map i).toAlgebra
    let _ : Algebra (A.source i) R := (A.sourceToLimit i).toAlgebra
    let _ : Algebra R S := f.toAlgebra
    let _ : Algebra (A.source i) S :=
      (f.comp (A.sourceToLimit i)).toAlgebra
    let _ : Algebra (A.target i) S := (A.targetToLimit i).toAlgebra
    let _ : IsScalarTower (A.source i) R S :=
      IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower (A.source i) (A.target i) S :=
    A.targetToLimit_isScalarTower i
    Algebra.IsPushout (A.source i) R (A.target i) S := sorry

/-- The canonical tensor-product algebra equivalence supplied by the final
pushout square.  Its source is oriented as `R ⊗[source i] target i`, matching
the standard `Algebra.IsPushout.equiv` orientation. -/
@[stacks 00R1 "directed approximation final pushout"]
noncomputable def finalTensorEquiv (A : Hom f)
    (hbc : A.baseChange_bijective) (i : A.index) :
    let _ : Algebra (A.source i) (A.target i) := (A.map i).toAlgebra
    let _ : Algebra (A.source i) R := (A.sourceToLimit i).toAlgebra
    let _ : Algebra R S := f.toAlgebra
    let _ : Algebra (A.source i) S :=
      (f.comp (A.sourceToLimit i)).toAlgebra
    let _ : Algebra (A.target i) S := (A.targetToLimit i).toAlgebra
    let _ : IsScalarTower (A.source i) R S :=
      IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower (A.source i) (A.target i) S :=
      A.targetToLimit_isScalarTower i
    TensorProduct (A.source i) R (A.target i) ≃ₐ[R] S :=
  let _ : Algebra (A.source i) (A.target i) := (A.map i).toAlgebra
  let _ : Algebra (A.source i) R := (A.sourceToLimit i).toAlgebra
  let _ : Algebra R S := f.toAlgebra
  let _ : Algebra (A.source i) S :=
    (f.comp (A.sourceToLimit i)).toAlgebra
  let _ : Algebra (A.target i) S := (A.targetToLimit i).toAlgebra
  let _ : IsScalarTower (A.source i) R S :=
    IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower (A.source i) (A.target i) S :=
    A.targetToLimit_isScalarTower i
  let _ : Algebra.IsPushout (A.source i) R (A.target i) S :=
    A.final_isPushout hbc i
  Algebra.IsPushout.equiv (A.source i) R (A.target i) S

/-- The final tensor-product algebra equivalence evaluates on pure tensors by
the two structure maps of the pushout square. -/
@[simp, stacks 00R1 "directed approximation final pushout"]
theorem finalTensorEquiv_tmul (A : Hom f)
    (hbc : A.baseChange_bijective) (i : A.index) (r : R) (t : A.target i) :
    let _ : Algebra (A.source i) (A.target i) := (A.map i).toAlgebra
    let _ : Algebra (A.source i) R := (A.sourceToLimit i).toAlgebra
    let _ : Algebra R S := f.toAlgebra
    let _ : Algebra (A.source i) S :=
      (f.comp (A.sourceToLimit i)).toAlgebra
    let _ : Algebra (A.target i) S := (A.targetToLimit i).toAlgebra
    let _ : IsScalarTower (A.source i) R S :=
      IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower (A.source i) (A.target i) S :=
      A.targetToLimit_isScalarTower i
    A.finalTensorEquiv hbc i (r ⊗ₜ[A.source i] t) =
      f r * A.targetToLimit i t := sorry

/-- The inverse final tensor equivalence sends the limiting map from the
source ring to the left tensor generator. -/
@[simp, stacks 00R1 "directed approximation final pushout"]
theorem finalTensorEquiv_symm_f (A : Hom f)
    (hbc : A.baseChange_bijective) (i : A.index) (r : R) :
    let _ : Algebra (A.source i) (A.target i) := (A.map i).toAlgebra
    let _ : Algebra (A.source i) R := (A.sourceToLimit i).toAlgebra
    let _ : Algebra R S := f.toAlgebra
    let _ : Algebra (A.source i) S :=
      (f.comp (A.sourceToLimit i)).toAlgebra
    let _ : Algebra (A.target i) S := (A.targetToLimit i).toAlgebra
    let _ : IsScalarTower (A.source i) R S :=
      IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower (A.source i) (A.target i) S :=
      A.targetToLimit_isScalarTower i
    (A.finalTensorEquiv hbc i).symm (f r) =
      r ⊗ₜ[A.source i] (1 : A.target i) := sorry

/-- The inverse final tensor equivalence sends the target-stage limiting map
to the right tensor generator. -/
@[simp, stacks 00R1 "directed approximation final pushout"]
theorem finalTensorEquiv_symm_target (A : Hom f)
    (hbc : A.baseChange_bijective) (i : A.index) (t : A.target i) :
    let _ : Algebra (A.source i) (A.target i) := (A.map i).toAlgebra
    let _ : Algebra (A.source i) R := (A.sourceToLimit i).toAlgebra
    let _ : Algebra R S := f.toAlgebra
    let _ : Algebra (A.source i) S :=
      (f.comp (A.sourceToLimit i)).toAlgebra
    let _ : Algebra (A.target i) S := (A.targetToLimit i).toAlgebra
    let _ : IsScalarTower (A.source i) R S :=
      IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower (A.source i) (A.target i) S :=
      A.targetToLimit_isScalarTower i
    (A.finalTensorEquiv hbc i).symm (A.targetToLimit i t) =
      (1 : R) ⊗ₜ[A.source i] t := sorry

/- The factor-swapped orientation is intentionally left to the canonical
tensor commutation equivalence at the use site; exporting it here would add a
second owner with a fragile algebra-instance pin. -/

end Ring.DirectLimit.Algebra.Approximation.Hom
