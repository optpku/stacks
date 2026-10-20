module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.FiniteTypeGeneration
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 70.9.2: let `S` be a scheme. Let `X` be a quasi-compact and quasi-separated algebraic
space over `S`. Let `F` be a quasi-coherent `𝒪_X`-module. Then `F` is the directed colimit of
its finite type quasi-coherent submodules. -/
@[stacks 0829] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.finiteTypeQuasiCoherentSubobjects_isDirectedColimit :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsQuasiCompact X]
      [IsAbsolutelyQuasiSeparated X] (F : X.Modules) [F.IsQuasicoherent],
      DirectedOn (· ≤ ·)
          (AlgebraicGeometry.AlgebraicSpace.Modules.finiteTypeQuasiCoherentSubobjects F) ∧
        IsLUB (AlgebraicGeometry.AlgebraicSpace.Modules.finiteTypeQuasiCoherentSubobjects F)
          (⊤ : Subobject F))
