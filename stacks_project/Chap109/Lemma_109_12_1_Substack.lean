/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Gorenstein

/-!
# The object property of Gorenstein families of curves

`𝒞urves^{Gorenstein}` is the full subcategory of families of curves whose
structure morphism is Gorenstein. Membership is the source-facing packaging of
a classifying morphism factoring through that open substack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.ObjectProperty
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.gorenstein :
    ∀ S : Scheme.{u}, ObjectProperty (Obj S))

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.gorenstein_iff :
    ∀ {S : Scheme.{u}} (P : Obj S),
      gorenstein S P ↔ AlgebraicSpace.Gorenstein (hom P))

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.instIsClosedUnderIsomorphisms_gorenstein :
    ∀ S : Scheme.{u}, (gorenstein S).IsClosedUnderIsomorphisms)

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

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
