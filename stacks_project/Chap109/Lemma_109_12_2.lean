/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.GorensteinDim1

/-!
# Gorenstein curves of relative dimension 1

There is an open substack `𝒞urves^{Gorenstein, 1} ⊂ 𝒞urves` classifying
Gorenstein families of curves of relative dimension 1, equivalently proper
Gorenstein schemes that are equidimensional of dimension 1 over a field.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/- Lemma 109.12.2: Gorenstein families of curves of exact relative dimension
one form an open substack, with the following membership characterizations. -/
@[stacks 0E6M] #check
  (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.exists_gorensteinDim1_open :
    ∀ {S : Scheme.{u}} (P : Obj S),
      ∃ U : (base P).left.Opens, ∀ {Q : Obj S} (φ : Q ⟶ P),
        gorensteinDim1 S Q ↔ Set.range (baseMap φ).left ⊆ U)

#check
  (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.gorensteinDim1_iff :
    ∀ {S : Scheme.{u}} (P : Obj S),
      gorensteinDim1 S P ↔
        AlgebraicSpace.Gorenstein (hom P) ∧ RelativeDimension (hom P) 1)

#check
  (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.classifying_factorsThrough_gorensteinDim1_iff_scheme :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
      [Nonempty X.left] (hdim : topologicalKrullDim X.left ≤ 1),
      gorensteinDim1 (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim) ↔
        Scheme.Gorenstein X.left ∧ EquidimensionalSpace X.left ∧
          topologicalKrullDim X.left = 1)

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
