/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Reflexive.Exact
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 31.12.7: let `X` be an integral locally Noetherian scheme and let
`0 → S.X₁ → S.X₂ → S.X₃` be exact with monic first map and coherent terms. If `S.X₂` is
reflexive and `S.X₃` is torsion-free, then `S.X₁` is reflexive. -/
@[stacks 0EBG] #check
  (AlgebraicGeometry.Scheme.Modules.IsReflexive.left_of_exact :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsIntegral X]
      [AlgebraicGeometry.IsLocallyNoetherian X]
      {S : CategoryTheory.ShortComplex X.Modules}
      [SheafOfModules.IsCoherent S.X₁] [SheafOfModules.IsCoherent S.X₂]
      [SheafOfModules.IsCoherent S.X₃]
      (_ : S.Exact) [CategoryTheory.Mono S.f]
      [AlgebraicGeometry.Scheme.Modules.IsReflexive S.X₂]
      [AlgebraicGeometry.Scheme.Modules.IsTorsionFree S.X₃],
      AlgebraicGeometry.Scheme.Modules.IsReflexive S.X₁)
