module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Flat.Criteria
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Flat

/-!
# Point-local finite-free factorizations

This leaf specializes the generic ringed-site flatness criterion to a single point of a ringed
space. The categorical factorization is the primary API; the finite-matrix statement is a
source-facing view for calculations with sections.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry
open scoped BigOperators

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Modules.FlatAt

variable {X : RingedSpace.{u}} (F : X.Modules)

/-- Lemma 17.17.11 (08BK), categorical form: a relation from the unit module to a finite free
module which vanishes in a module flat at `x` factors near `x` through another finite free module
on which the relation already vanishes. -/
@[stacks 08BK "categorical factorization"]
theorem existsFactorization {U : Opens X} {I : Type u} [Finite I]
    (α : SheafOfModules.unit (X.ringCatSheaf.over U) ⟶
      (SheafOfModules.free.{u} I : SheafOfModules _))
    (β : (SheafOfModules.free.{u} I : SheafOfModules _) ⟶ F.over U)
    (hcomplex : α ≫ β = 0) (x : X) (hx : x ∈ U) (hflat : F.IsFlatAt x) :
    ∃ (V : Over U) (_ : x ∈ V.left) (J : Type u) (_ : Finite J)
      (A : ((SheafOfModules.free.{u} I : SheafOfModules (X.ringCatSheaf.over U)).over V) ⟶
        (SheafOfModules.free.{u} J : SheafOfModules ((X.ringCatSheaf.over U).over V)))
      (γ : (SheafOfModules.free.{u} J : SheafOfModules ((X.ringCatSheaf.over U).over V)) ⟶
        (F.over U).over V),
      β.over V = A ≫ γ ∧ α.over V ≫ A = 0 := sorry

/-- Lemma 17.17.11 (08BK), matrix form: a finite relation among sections of a module flat at
`x` admits, after shrinking around `x`, a finite matrix factorization whose columns annihilate
the restricted coefficient relation. -/
@[stacks 08BK "matrix factorization"]
theorem existsMatrixFactorization {U : Opens X} {n : ℕ}
    (f : Fin n → X.presheaf.obj (op U)) (s : Fin n → F.val.obj (op U))
    (hcomplex : ∑ i, f i • s i = 0) (x : X) (hx : x ∈ U) (hflat : F.IsFlatAt x) :
    ∃ (V : Opens X) (_ : x ∈ V) (hVU : V ≤ U) (m : ℕ)
      (A : Fin n → Fin m → X.presheaf.obj (op V))
      (t : Fin m → F.val.obj (op V)),
      (∀ i, F.val.map (homOfLE hVU).op (s i) = ∑ j, A i j • t j) ∧
        ∀ j, ∑ i, X.presheaf.map (homOfLE hVU).op (f i) * A i j = 0 := sorry

end AlgebraicGeometry.RingedSpace.Modules.FlatAt
