/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Gorenstein

/-!
# Gorenstein curves

There is an open substack 𝒞urves^{Gorenstein} ⊂ 𝒞urves classifying Gorenstein
families of curves, equivalently proper Gorenstein schemes of dimension at most
one over a field.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/- Lemma 109.12.1. Gorenstein families of curves form an open substack,
with membership characterized by the structure morphism and, over a field,
by Gorensteinness of the proper scheme of dimension at most one. -/
@[stacks 0E1M] #check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.exists_gorenstein_open :
    ∀ {S : Scheme.{u}} (P : Obj S),
      ∃ U : (base P).left.Opens, ∀ {Q : Obj S} (φ : Q ⟶ P),
        gorenstein S Q ↔ Set.range (baseMap φ).left ⊆ U)

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.gorenstein_iff :
    ∀ {S : Scheme.{u}} (P : Obj S),
      gorenstein S P ↔ AlgebraicSpace.Gorenstein (hom P))

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.classifying_factorsThrough_gorenstein_iff_scheme :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
      (hdim : topologicalKrullDim X.left ≤ 1),
      gorenstein (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim) ↔
        Scheme.Gorenstein X.left)

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.instIsFiberedInGroupoids_gorenstein :
    ∀ S : Scheme.{u},
      Functor.IsFibered.InGroupoids ((gorenstein S).ι ⋙ p S))

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
