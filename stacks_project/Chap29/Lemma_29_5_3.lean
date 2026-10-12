/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Support
import StacksCheckRecall

open AlgebraicGeometry
open scoped AlgebraicGeometry TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]

/- Lemma 29.5.3 (1): the support of a finite-type quasi-coherent module sheaf is closed. -/
@[stacks 056J] #check (AlgebraicGeometry.Scheme.Modules.isClosed_moduleSupport ℱ :
  IsClosed (AlgebraicGeometry.Scheme.Modules.moduleSupport ℱ))

/- Support membership is equivalent to the existence of a nonzero stalk element. -/
#check (AlgebraicGeometry.RingedSpace.mem_moduleSupport_iff ℱ :
  ∀ x : X, x ∈ AlgebraicGeometry.Scheme.Modules.moduleSupport ℱ ↔
    ∃ m : AlgebraicGeometry.RingedSpace.stalkModuleCat ℱ x, m ≠ 0)

/- Support membership is equivalent to nontriviality of the residue-field fiber. -/
#check (AlgebraicGeometry.Scheme.Modules.mem_moduleSupport_iff_nontrivial_fiber ℱ :
  ∀ x : X, x ∈ AlgebraicGeometry.Scheme.Modules.moduleSupport ℱ ↔
    Nontrivial
      (IsLocalRing.ResidueField (X.presheaf.stalk x) ⊗[X.presheaf.stalk x]
        AlgebraicGeometry.RingedSpace.stalkModuleCat ℱ x))

variable (f : Y ⟶ X)

/- Pullback preserves finite type. -/
#check (AlgebraicGeometry.Scheme.Modules.pullback_isFiniteType f ℱ :
  ((AlgebraicGeometry.Scheme.Modules.pullback f).obj ℱ).IsFiniteType)

/- The support of a pullback is the inverse image of the original support. -/
#check (AlgebraicGeometry.Scheme.Modules.moduleSupport_pullback_eq_preimage ℱ f :
  AlgebraicGeometry.Scheme.Modules.moduleSupport
      ((AlgebraicGeometry.Scheme.Modules.pullback f).obj ℱ) =
    f.base ⁻¹' AlgebraicGeometry.Scheme.Modules.moduleSupport ℱ)

end AlgebraicGeometry.Scheme.Modules
