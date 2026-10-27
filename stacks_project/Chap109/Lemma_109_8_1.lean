/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.CohenMacaulay
import StacksCheckRecall

/-!
# Cohen–Macaulay curves

There is an open substack 𝒞urves^{CM} ⊂ 𝒞urves classifying Cohen–Macaulay
families of curves, equivalently proper Cohen–Macaulay schemes of dimension
at most one over a field.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

/- Lemma 109.8.1: the Cohen–Macaulay substack is represented by an open of
any family's base, compatibly with every cartesian morphism of families. -/
@[stacks 0E0I] #check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.exists_cohenMacaulay_open :
  ∀ {S : Scheme.{u}} (P : Obj S), ∃ U : (base P).left.Opens,
    ∀ {Q : Obj S} (φ : Q ⟶ P),
      cohenMacaulay S Q ↔ Set.range (baseMap φ).left ⊆ U)

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.cohenMacaulay_iff :
  ∀ {S : Scheme.{u}} (P : Obj S),
    cohenMacaulay S P ↔ AlgebraicSpace.CohenMacaulay (hom P))

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.classifying_factorsThrough_cohenMacaulay_iff_scheme :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1),
    cohenMacaulay (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim) ↔
      Scheme.CohenMacaulay X.left)

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
