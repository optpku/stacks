/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.H0Dim1
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.OverField
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Flat

/-!
# The object property of curves with universally trivial pushforward of 𝒪

The canonical curve owners provide the property, its isomorphism invariance,
and the construction of curve families from proper schemes over a field.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.h0Dim1 :
    ∀ S : Scheme.{u}, ObjectProperty (Obj S))

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.h0Dim1_iff :
    ∀ {S : Scheme.{u}} (P : Obj S),
      h0Dim1 S P ↔
        (∀ {Z : AlgebraicSpace S} (g : Z ⟶ ofOver (base P)),
            IsIso (Modules.unitToPushforwardObjUnit (pullback.snd (hom P) g))) ∧
          ∀ y : Points (ofOver (base P)), fiberDimension (hom P) y = 1)

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.instIsClosedUnderIsomorphisms_h0Dim1 :
    ∀ S : Scheme.{u}, (h0Dim1 S).IsClosedUnderIsomorphisms)

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.schemeOverFieldHom :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k),
      ofOver (Over.mk X.hom) ⟶
        ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k)))))

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.schemeOverFieldHom_eq :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k),
      schemeOverFieldHom X = ofOverHomMk X.hom (Category.comp_id X.hom))

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.instFpFlatProper_schemeOverFieldHom :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom],
      FpFlatProper (schemeOverFieldHom X))

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.relativeDimensionLE_schemeOverFieldHom :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
      (hdim : topologicalKrullDim X.left ≤ 1),
      RelativeDimensionLE (schemeOverFieldHom X) 1)

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.mkOfSchemeOverField :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
      (hdim : topologicalKrullDim X.left ≤ 1),
      Obj (Spec (CommRingCat.of k)))

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.mkOfSchemeOverField_hom :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
      (hdim : topologicalKrullDim X.left ≤ 1),
      hom (mkOfSchemeOverField X hdim) = schemeOverFieldHom X)

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
