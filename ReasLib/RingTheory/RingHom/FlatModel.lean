/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.RingHom.FinitePresentation
public import Mathlib.RingTheory.RingHom.FiniteType
public import ReasLib.Algebra.Module.Flat.Relative
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open scoped TensorProduct

universe uR uS uR₀ uS₀ uM uM₀

namespace RingHom

set_option linter.checkUnivs false in
/-- 02JO: a flat module model over a commutative-ring map.

The source map `r`, stage map `stageMap`, and target map `targetMap` are
explicit parameters; their commutativity equation is a field of the model.
The structure owns the comparison map, the ring pushout square, the module
base-change condition, and flatness along the stage map. Finite-type and
finite-presentation predicates add only their respective finiteness data,
since flatness is already part of every `FlatModel`. -/
@[stacks 02JO "flat module model with pushout and base change"]
structure FlatModel
    {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]
    (f : R →+* S) {M : Type uM} [AddCommGroup M] [Module S M]
    {R₀ : Type uR₀} [CommRing R₀] (r : R₀ →+* R)
    {S₀ : Type uS₀} [CommRing S₀] (stageMap : R₀ →+* S₀)
    {M₀ : Type uM₀} [AddCommGroup M₀] [Module S₀ M₀]
    (targetMap : S₀ →+* S) where
  /-- The two composites from the source stage to the limiting target agree. -/
  comm : targetMap.comp stageMap = f.comp r
  /-- The module comparison from the stage module to the limiting module. -/
  comparison :
    let _ : Module S₀ M := Module.compHom M targetMap
    M₀ →ₗ[S₀] M
  /-- The ring square determined by the model is a pushout. -/
  pushout :
    let _ : Algebra R₀ R := r.toAlgebra
    let _ : Algebra R₀ S₀ := stageMap.toAlgebra
    let _ : Algebra R S := f.toAlgebra
    let _ : Algebra S₀ S := targetMap.toAlgebra
    let _ : Algebra R₀ S := (f.comp r).toAlgebra
    let _ : IsScalarTower R₀ R S := IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower R₀ S₀ S := IsScalarTower.of_algebraMap_eq' comm.symm
    Algebra.IsPushout R₀ R S₀ S
  /-- The module comparison realizes the limiting module by base change. -/
  baseChange :
    let _ : Algebra S₀ S := targetMap.toAlgebra
    let _ : Module S₀ M := Module.compHom M targetMap
    let _ : IsScalarTower S₀ S M :=
      @IsScalarTower.of_compHom S₀ S M _ _ targetMap.toAlgebra _
    IsBaseChange S comparison
  /-- The stage module is flat after restriction along the stage map. -/
  flat : Module.FlatAlong stageMap M₀

namespace FlatModel

variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]
variable {f : R →+* S} {M : Type uM} [AddCommGroup M] [Module S M]
variable {R₀ : Type uR₀} [CommRing R₀] {r : R₀ →+* R}
variable {S₀ : Type uS₀} [CommRing S₀] {stageMap : R₀ →+* S₀}
variable {M₀ : Type uM₀} [AddCommGroup M₀] [Module S₀ M₀]
variable {targetMap : S₀ →+* S}

/-- The source stage of a flat model is finite type over `ℤ`. -/
@[stacks 02JO "flat module model source finiteness"]
def sourceFiniteType (P : FlatModel (M := M) (M₀ := M₀) f r stageMap targetMap) : Prop :=
  (Int.castRingHom R₀).FiniteType

/-- The stage map of a flat model is finite type. -/
@[stacks 02JO "flat module model stage finite type"]
def stageFiniteType (P : FlatModel (M := M) (M₀ := M₀) f r stageMap targetMap) : Prop :=
  stageMap.FiniteType

/-- The stage module of a flat model is finite. -/
@[stacks 02JO "flat module model module finiteness"]
def moduleFinite (P : FlatModel (M := M) (M₀ := M₀) f r stageMap targetMap) : Prop :=
  Module.Finite S₀ M₀

/-- The stage map of a flat model is finitely presented. -/
@[stacks 02JO "flat module model stage finite presentation"]
def stageFinitePresentation
    (P : FlatModel (M := M) (M₀ := M₀) f r stageMap targetMap) : Prop :=
  stageMap.FinitePresentation

/-- The stage module of a flat model is finitely presented. -/
@[stacks 02JO "flat module model module finite presentation"]
def moduleFinitePresentation
    (P : FlatModel (M := M) (M₀ := M₀) f r stageMap targetMap) : Prop :=
  Module.FinitePresentation S₀ M₀

/-- The finiteness data of a finite-type flat model.

Flatness is supplied directly by `P.flat`. -/
@[stacks 02JO "finite-type flat module model"]
def finiteType (P : FlatModel (M := M) (M₀ := M₀) f r stageMap targetMap) : Prop :=
  P.sourceFiniteType ∧ P.stageFiniteType ∧ P.moduleFinite

/-- The finiteness data of a finitely presented flat model.

Flatness is supplied directly by `P.flat`. -/
@[stacks 02JO "finite-presentation flat module model"]
def finitePresentation
    (P : FlatModel (M := M) (M₀ := M₀) f r stageMap targetMap) : Prop :=
  P.stageFinitePresentation ∧ P.moduleFinitePresentation

/-- Extract the source finite-type condition from a finite-type model. -/
@[stacks 02JO "finite-type flat module model"]
theorem finiteType_source
    (P : FlatModel (M := M) (M₀ := M₀) f r stageMap targetMap)
    (hP : P.finiteType) : P.sourceFiniteType := sorry

/-- Extract the stage-map finite-type condition from a finite-type model. -/
@[stacks 02JO "finite-type flat module model"]
theorem finiteType_stage
    (P : FlatModel (M := M) (M₀ := M₀) f r stageMap targetMap)
    (hP : P.finiteType) : P.stageFiniteType := sorry

/-- Extract the stage-module finiteness condition from a finite-type model. -/
@[stacks 02JO "finite-type flat module model"]
theorem finiteType_module
    (P : FlatModel (M := M) (M₀ := M₀) f r stageMap targetMap)
    (hP : P.finiteType) : P.moduleFinite := sorry

/-- Extract the stage-map finite-presentation condition from a finite-presentation model. -/
@[stacks 02JO "finite-presentation flat module model"]
theorem finitePresentation_stage
    (P : FlatModel (M := M) (M₀ := M₀) f r stageMap targetMap)
    (hP : P.finitePresentation) : P.stageFinitePresentation := sorry

/-- Extract the stage-module finite-presentation condition from a finite-presentation model. -/
@[stacks 02JO "finite-presentation flat module model"]
theorem finitePresentation_module
    (P : FlatModel (M := M) (M₀ := M₀) f r stageMap targetMap)
    (hP : P.finitePresentation) : P.moduleFinitePresentation := sorry

/-- The ring pushout equivalence carried by a flat model. -/
@[stacks 02JO "flat module model pushout equivalence"]
noncomputable def pushoutEquiv
    (P : FlatModel (M := M) (M₀ := M₀) f r stageMap targetMap) :
    let _ : Algebra R₀ R := r.toAlgebra
    let _ : Algebra R₀ S₀ := stageMap.toAlgebra
    let _ : Algebra R S := f.toAlgebra
    let _ : Algebra S₀ S := targetMap.toAlgebra
    let _ : Algebra R₀ S := (f.comp r).toAlgebra
    let _ : IsScalarTower R₀ R S := IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower R₀ S₀ S := IsScalarTower.of_algebraMap_eq' P.comm.symm
    R ⊗[R₀] S₀ ≃ₐ[R] S :=
  let _ : Algebra R₀ R := r.toAlgebra
  let _ : Algebra R₀ S₀ := stageMap.toAlgebra
  let _ : Algebra R S := f.toAlgebra
  let _ : Algebra S₀ S := targetMap.toAlgebra
  let _ : Algebra R₀ S := (f.comp r).toAlgebra
  let _ : IsScalarTower R₀ R S := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower R₀ S₀ S := IsScalarTower.of_algebraMap_eq' P.comm.symm
  let _ : Algebra.IsPushout R₀ R S₀ S := P.pushout
  Algebra.IsPushout.equiv R₀ R S₀ S

/-- The pushout equivalence evaluates on pure tensors by the two structure maps. -/
@[simp, stacks 02JO "flat module model pushout equivalence"]
theorem pushoutEquiv_tmul
    (P : FlatModel (M := M) (M₀ := M₀) f r stageMap targetMap)
    (x : R) (y : S₀) :
    let _ : Algebra R₀ R := r.toAlgebra
    let _ : Algebra R₀ S₀ := stageMap.toAlgebra
    let _ : Algebra R S := f.toAlgebra
    let _ : Algebra S₀ S := targetMap.toAlgebra
    let _ : Algebra R₀ S := (f.comp r).toAlgebra
    let _ : IsScalarTower R₀ R S := IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower R₀ S₀ S := IsScalarTower.of_algebraMap_eq' P.comm.symm
    P.pushoutEquiv (x ⊗ₜ[R₀] y) = f x * targetMap y := sorry

/-- The inverse pushout equivalence sends the image under `f` to the left
tensor generator. -/
@[simp, stacks 02JO "flat module model pushout equivalence"]
theorem pushoutEquiv_symm_f
    (P : FlatModel (M := M) (M₀ := M₀) f r stageMap targetMap)
    (x : R) :
    let _ : Algebra R₀ R := r.toAlgebra
    let _ : Algebra R₀ S₀ := stageMap.toAlgebra
    let _ : Algebra R S := f.toAlgebra
    let _ : Algebra S₀ S := targetMap.toAlgebra
    let _ : Algebra R₀ S := (f.comp r).toAlgebra
    let _ : IsScalarTower R₀ R S := IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower R₀ S₀ S := IsScalarTower.of_algebraMap_eq' P.comm.symm
    (P.pushoutEquiv).symm (f x) = x ⊗ₜ[R₀] (1 : S₀) := sorry

/-- The inverse pushout equivalence sends the target-stage map to the right
tensor generator. -/
@[simp, stacks 02JO "flat module model pushout equivalence"]
theorem pushoutEquiv_symm_targetMap
    (P : FlatModel (M := M) (M₀ := M₀) f r stageMap targetMap)
    (y : S₀) :
    let _ : Algebra R₀ R := r.toAlgebra
    let _ : Algebra R₀ S₀ := stageMap.toAlgebra
    let _ : Algebra R S := f.toAlgebra
    let _ : Algebra S₀ S := targetMap.toAlgebra
    let _ : Algebra R₀ S := (f.comp r).toAlgebra
    let _ : IsScalarTower R₀ R S := IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower R₀ S₀ S := IsScalarTower.of_algebraMap_eq' P.comm.symm
    (P.pushoutEquiv).symm (targetMap y) = (1 : R) ⊗ₜ[R₀] y := sorry

/-- The tensor-product equivalence supplied by the model's base-change field.
The scalar and module actions are induced by `targetMap` and are kept local to
the returned equivalence. -/
@[stacks 02JO "flat module model comparison equivalence"]
noncomputable def comparisonEquiv
    (P : FlatModel (M := M) (M₀ := M₀) f r stageMap targetMap) :
    let _ : Algebra S₀ S := targetMap.toAlgebra
    let _ : Module S₀ M := Module.compHom M targetMap
    let _ : IsScalarTower S₀ S M :=
      @IsScalarTower.of_compHom S₀ S M _ _ targetMap.toAlgebra _
    S ⊗[S₀] M₀ ≃ₗ[S] M :=
  let _ : Algebra S₀ S := targetMap.toAlgebra
  let _ : Module S₀ M := Module.compHom M targetMap
  let _ : IsScalarTower S₀ S M :=
    @IsScalarTower.of_compHom S₀ S M _ _ targetMap.toAlgebra _
  P.baseChange.equiv

/-- The comparison equivalence evaluates on pure tensors by scalar action. -/
@[simp, stacks 02JO "flat module model comparison equivalence"]
theorem comparisonEquiv_tmul
    (P : FlatModel (M := M) (M₀ := M₀) f r stageMap targetMap)
    (s : S) (m : M₀) :
    let _ : Algebra S₀ S := targetMap.toAlgebra
    let _ : Module S₀ M := Module.compHom M targetMap
    let _ : IsScalarTower S₀ S M :=
      @IsScalarTower.of_compHom S₀ S M _ _ targetMap.toAlgebra _
    P.comparisonEquiv (s ⊗ₜ[S₀] m) = s • P.comparison m := sorry

/-- The comparison equivalence sends the canonical tensor generator to the
original stage-module comparison. -/
@[simp, stacks 02JO "flat module model comparison equivalence"]
theorem comparisonEquiv_one_tmul
    (P : FlatModel (M := M) (M₀ := M₀) f r stageMap targetMap)
    (m : M₀) :
    let _ : Algebra S₀ S := targetMap.toAlgebra
    let _ : Module S₀ M := Module.compHom M targetMap
    let _ : IsScalarTower S₀ S M :=
      @IsScalarTower.of_compHom S₀ S M _ _ targetMap.toAlgebra _
    P.comparisonEquiv (1 ⊗ₜ[S₀] m) = P.comparison m := sorry

/-- The inverse comparison equivalence sends a stage-module comparison to its
canonical tensor generator. -/
@[simp, stacks 02JO "flat module model comparison equivalence"]
theorem comparisonEquiv_symm_comparison
    (P : FlatModel (M := M) (M₀ := M₀) f r stageMap targetMap)
    (m : M₀) :
    let _ : Algebra S₀ S := targetMap.toAlgebra
    let _ : Module S₀ M := Module.compHom M targetMap
    let _ : IsScalarTower S₀ S M :=
      @IsScalarTower.of_compHom S₀ S M _ _ targetMap.toAlgebra _
    (P.comparisonEquiv).symm (P.comparison m) = (1 : S) ⊗ₜ[S₀] m := sorry

/-- Pointwise form of the square-commutativity equation. -/
@[stacks 02JO "flat module model commutativity"]
theorem comm_apply
    (P : FlatModel (M := M) (M₀ := M₀) f r stageMap targetMap) (x : R₀) :
    targetMap (stageMap x) = f (r x) := sorry

/-- The defining data and properties of a flat model, exposed as one
source-facing specification theorem. -/
@[stacks 02JO "flat module model specification"]
theorem spec (P : FlatModel (M := M) (M₀ := M₀) f r stageMap targetMap) :
    targetMap.comp stageMap = f.comp r ∧
      (let _ : Algebra R₀ R := r.toAlgebra
       let _ : Algebra R₀ S₀ := stageMap.toAlgebra
       let _ : Algebra R S := f.toAlgebra
       let _ : Algebra S₀ S := targetMap.toAlgebra
       let _ : Algebra R₀ S := (f.comp r).toAlgebra
       let _ : IsScalarTower R₀ R S := IsScalarTower.of_algebraMap_eq' rfl
       let _ : IsScalarTower R₀ S₀ S := IsScalarTower.of_algebraMap_eq' P.comm.symm
       Algebra.IsPushout R₀ R S₀ S) ∧
      (let _ : Algebra S₀ S := targetMap.toAlgebra
       let _ : Module S₀ M := Module.compHom M targetMap
       let _ : IsScalarTower S₀ S M :=
         @IsScalarTower.of_compHom S₀ S M _ _ targetMap.toAlgebra _
       IsBaseChange S P.comparison) ∧
      Module.FlatAlong stageMap M₀ := sorry

end FlatModel

end RingHom
