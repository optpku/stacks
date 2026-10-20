/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Length.Point
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.AssociatedCycle
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

universe u

section

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
variable (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
variable (δ : Points B → ℤ) [IsDimensionFunction δ]

/- Definition 82.6.1 (1): In Situation 82.2.1, for good `X / B` and a coherent
`𝒪_X`-module `F`, the multiplicity of an integral closed subspace `Z ⊂ X` whose
`|Z|` is an irreducible component of `moduleSupport F` is the length of `F` at
the generic point of `Z`. -/
@[stacks 0EEB]
#check (AlgebraicGeometry.AlgebraicSpace.Modules.componentMultiplicity :
  {S : Scheme.{u}} → {X : AlgebraicSpace S} →
    [IsLocallyNoetherian X] → [IsDecent X] →
    (F : X.Modules) → [F.IsCoherent] → (x : Points X) →
      IsGenericPoint.ofIrreducibleComponent x (moduleSupport F) → ℕ)

/- Definition 82.6.1 (2): If `dim_δ(moduleSupport F) ≤ k`, the associated `k`-cycle
is the multiplicity-weighted sum of the `δ`-dimension-`k` irreducible components
of `moduleSupport F`. -/
@[stacks 0EEB]
#check (AlgebraicGeometry.AlgebraicSpace.Hom.moduleCycle f δ :
  (F : X.Modules) → [F.IsCoherent] → (k : ℤ) →
    AlgebraicGeometry.AlgebraicSpace.Hom.moduleSupportDeltaDimension f δ F ≤ (k : EInt) →
      Function.locallyFinsupp (Points X) ℤ)

#check (AlgebraicGeometry.AlgebraicSpace.Hom.moduleCycle_mem f δ :
  (F : X.Modules) → [F.IsCoherent] → (k : ℤ) →
    (hF : AlgebraicGeometry.AlgebraicSpace.Hom.moduleSupportDeltaDimension f δ F ≤
      (k : EInt)) →
      AlgebraicGeometry.AlgebraicSpace.Hom.moduleCycle f δ F k hF ∈
        AlgebraicGeometry.AlgebraicSpace.Hom.cycleGroup f δ k)

end
