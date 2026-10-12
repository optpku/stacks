/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.FiniteTypeGeneration
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 28.22.3: let `X` be a quasi-compact and quasi-separated scheme. Any quasi-coherent
module on `X` is the directed colimit of its quasi-coherent submodules of finite type. -/
@[stacks 01PG] #check
  (AlgebraicGeometry.Scheme.Modules.finiteTypeQuasiCoherentSubobjects_isDirectedColimit :
    ∀ {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      (F : X.Modules) [F.IsQuasicoherent],
      DirectedOn (· ≤ ·)
          (AlgebraicGeometry.Scheme.Modules.finiteTypeQuasiCoherentSubobjects F) ∧
        IsLUB (AlgebraicGeometry.Scheme.Modules.finiteTypeQuasiCoherentSubobjects F)
          (⊤ : Subobject F))
