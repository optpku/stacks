/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.CohenMacaulayDim1
import StacksCheckRecall

/-!
# Cohen–Macaulay curves of relative dimension 1

There is an open substack `𝒞urves^{CM, 1} ⊂ 𝒞urves` classifying Cohen–Macaulay
families of curves of relative dimension 1, equivalently proper Cohen–Macaulay
schemes that are equidimensional of dimension 1 over a field.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/- Lemma 109.8.2: the Cohen–Macaulay families of curves of relative dimension
one form an open substack, represented universally by opens of family bases. -/
@[stacks 0E1F] #check
  (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.exists_cohenMacaulayDim1_open :
    ∀ {S : Scheme.{u}} (P : Obj S),
      ∃ U : (base P).left.Opens, ∀ {Q : Obj S} (φ : Q ⟶ P),
        cohenMacaulayDim1 S Q ↔ Set.range (baseMap φ).left ⊆ U)

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.cohenMacaulayDim1_iff :
  ∀ {S : Scheme.{u}} (P : Obj S),
    cohenMacaulayDim1 S P ↔
      AlgebraicSpace.CohenMacaulay (hom P) ∧ RelativeDimension (hom P) 1)

#check
  (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.classifying_factorsThrough_cohenMacaulayDim1_iff_scheme :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
      [Nonempty X.left] (hdim : topologicalKrullDim X.left ≤ 1),
      cohenMacaulayDim1 (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim) ↔
        Scheme.CohenMacaulay X.left ∧ EquidimensionalSpace X.left ∧
          topologicalKrullDim X.left = 1)

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
