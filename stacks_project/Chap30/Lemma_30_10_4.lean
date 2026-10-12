/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.FiniteTypeGeneration
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 30.10.4: let `X` be a Noetherian scheme. Every quasi-coherent
`𝒪_X`-module is the filtered colimit of its coherent submodules. -/
@[stacks 0GN6] #check
  (AlgebraicGeometry.Scheme.Modules.finiteTypeQuasiCoherentSubobjects_isDirectedColimit :
    ∀ {X : Scheme.{u}} [IsNoetherian X]
      (F : X.Modules) [F.IsQuasicoherent],
      DirectedOn (· ≤ ·)
          (AlgebraicGeometry.Scheme.Modules.finiteTypeQuasiCoherentSubobjects F) ∧
        IsLUB (AlgebraicGeometry.Scheme.Modules.finiteTypeQuasiCoherentSubobjects F)
          (⊤ : Subobject F))

#check
  (AlgebraicGeometry.Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType :
    ∀ {X : Scheme.{u}} [IsNoetherian X] (F : X.Modules),
      F.IsCoherent ↔ F.IsQuasicoherent ∧ F.IsFiniteType)
