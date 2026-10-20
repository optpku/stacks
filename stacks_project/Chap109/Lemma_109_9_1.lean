module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.H0Dim1

/-!
# Curves with universally trivial pushforward of 𝒪 and fibres of dimension 1

The condition defines an open substack of curves and is characterized over a
field by the canonical global-sections map and dimension one.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

/- Lemma 109.9.1. The condition of universally trivial structure-sheaf pushforward
and fibres of dimension one defines an open substack, with the following family
and field-valued characterizations. -/
@[stacks 0E6I] #check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.exists_h0Dim1_open :
    ∀ {S : Scheme.{u}} (P : Obj S),
      ∃ U : (base P).left.Opens, ∀ {Q : Obj S} (φ : Q ⟶ P),
        h0Dim1 S Q ↔ Set.range (baseMap φ).left ⊆ U)

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.h0Dim1_iff :
    ∀ {S : Scheme.{u}} (P : Obj S),
      h0Dim1 S P ↔
        (∀ {Z : AlgebraicSpace S} (g : Z ⟶ ofOver (base P)),
            IsIso (Modules.unitToPushforwardObjUnit (pullback.snd (hom P) g))) ∧
          ∀ y : Points (ofOver (base P)), fiberDimension (hom P) y = 1)

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.classifying_factorsThrough_h0Dim1_iff_scheme :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
      (hdim : topologicalKrullDim X.left ≤ 1),
      h0Dim1 (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim) ↔
        Function.Bijective (Scheme.Hom.globalSectionsMap X.hom) ∧
          topologicalKrullDim X.left = 1)

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
