module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Nodal

/-!
# The object property of at-worst-nodal families of curves

The nodal object property and the canonical families associated to proper
schemes over fields are provided by the shared curve owners.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.ObjectProperty
open AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.nodal :
  ∀ S : Scheme.{u}, ObjectProperty (Obj S))

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.nodal_iff :
  ∀ {S : Scheme.{u}} (P : Obj S),
    nodal S P ↔ AlgebraicSpace.AtWorstNodal (hom P))

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.instIsClosedUnderIsomorphisms_nodal :
  ∀ S : Scheme.{u}, (nodal S).IsClosedUnderIsomorphisms)

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
  ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom],
    topologicalKrullDim X.left ≤ 1 → RelativeDimensionLE (schemeOverFieldHom X) 1)

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.mkOfSchemeOverField :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom],
    topologicalKrullDim X.left ≤ 1 → Obj (Spec (CommRingCat.of k)))

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.mkOfSchemeOverField_hom :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1),
    hom (mkOfSchemeOverField X hdim) = schemeOverFieldHom X)

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
