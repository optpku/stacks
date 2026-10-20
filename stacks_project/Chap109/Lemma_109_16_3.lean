/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.SmoothH0

/-!
# Smooth curves with universally trivial pushforward of 𝒪

There is an open substack `𝒞urves^{smooth, h0} ⊂ 𝒞urves` classifying smooth
families of curves with universally trivial `𝒪_S ⟶ f_* 𝒪_X`, equivalently
proper smooth schemes of dimension one over a field with `k = H⁰(X, 𝒪_X)`,
equivalently geometrically connected, equivalently geometrically integral,
equivalently becoming a smooth curve after base change to an algebraic
closure.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

/- Lemma 109.16.3. Smooth families of curves with universally trivial
structure-sheaf pushforward and fibres of dimension one form an open substack,
with the following family and field-valued characterizations. -/
@[stacks 0E81] #check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.exists_smoothH0_open :
    ∀ {S : Scheme.{u}} (P : Obj S),
      ∃ U : (base P).left.Opens, ∀ {Q : Obj S} (φ : Q ⟶ P),
        smoothH0 S Q ↔ Set.range (baseMap φ).left ⊆ U)

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.smoothH0_iff :
    ∀ {S : Scheme.{u}} (P : Obj S),
      smoothH0 S P ↔
        (∀ {Z : AlgebraicSpace S} (g : Z ⟶ ofOver (base P)),
            IsIso (Modules.unitToPushforwardObjUnit (pullback.snd (hom P) g))) ∧
          AlgebraicSpace.Smooth (hom P) ∧ RelativeDimension (hom P) 1)

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.classifying_factorsThrough_smoothH0_tfae_scheme :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1),
    List.TFAE
      [smoothH0 (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim),
        AlgebraicGeometry.Smooth X.hom ∧ topologicalKrullDim X.left = 1 ∧
          Function.Bijective (Scheme.Hom.globalSectionsMap X.hom),
        AlgebraicGeometry.Smooth X.hom ∧ topologicalKrullDim X.left = 1 ∧
          GeometricallyConnected X.hom,
        AlgebraicGeometry.Smooth X.hom ∧ topologicalKrullDim X.left = 1 ∧
          GeometricallyIntegral X.hom,
        Curve (FieldExtension.Over.baseChange k (AlgebraicClosure k) X) ∧
          AlgebraicGeometry.Smooth (FieldExtension.Over.baseChange k (AlgebraicClosure k) X).hom])

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
