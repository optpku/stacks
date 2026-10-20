module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import ReasLib.AlgebraicGeometry.Scheme.DescentData.Etale
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry
namespace Scheme.Etale

/-- The property of an étale scheme over `S` that its structure morphism is
quasi-compact and separated. -/
abbrev qcSeparatedProperty (S : Scheme.{u}) : ObjectProperty S.Etale :=
  fun U ↦ (@AlgebraicGeometry.QuasiCompact ⊓ @AlgebraicGeometry.IsSeparated) U.hom

/-- Membership in `qcSeparatedProperty S` is exactly quasi-compactness and separatedness
of the structure morphism. -/
theorem qcSeparatedProperty_iff (S : Scheme.{u}) (U : S.Etale) :
    qcSeparatedProperty S U ↔ QuasiCompact U.hom ∧ IsSeparated U.hom := sorry

namespace qcSeparatedProperty

/-- An object of the quasi-compact separated full subcategory has quasi-compact structure
morphism. -/
instance quasiCompact (S : Scheme.{u})
    (U : (qcSeparatedProperty S).FullSubcategory) : QuasiCompact U.obj.hom := sorry

/-- An object of the quasi-compact separated full subcategory has separated structure
morphism. -/
instance isSeparated (S : Scheme.{u})
    (U : (qcSeparatedProperty S).FullSubcategory) : IsSeparated U.obj.hom := sorry

end qcSeparatedProperty

end Scheme.Etale

namespace Scheme.DescentData.Etale

variable {X S : Scheme.{u}}

/-- The property that the unique component of an étale descent datum is quasi-compact
and separated over the covering scheme. -/
abbrev qcSeparatedProperty (f : X ⟶ S) : ObjectProperty (Etale f) :=
  fun D ↦ (@AlgebraicGeometry.QuasiCompact ⊓ @AlgebraicGeometry.IsSeparated)
    (D.obj.obj PUnit.unit).hom

/-- Membership in `qcSeparatedProperty f` is exactly quasi-compactness and separatedness
of the unique component morphism. -/
theorem qcSeparatedProperty_iff (f : X ⟶ S) (D : Etale f) :
    qcSeparatedProperty f D ↔
      QuasiCompact (D.obj.obj PUnit.unit).hom ∧
        IsSeparated (D.obj.obj PUnit.unit).hom := sorry

namespace qcSeparatedProperty

/-- Quasi-compactness and separatedness of the component are invariant under isomorphism
of étale descent data. -/
instance isClosedUnderIsomorphisms (f : X ⟶ S) :
    (qcSeparatedProperty f).IsClosedUnderIsomorphisms := sorry

/-- A selected étale descent datum has quasi-compact component morphism. -/
instance quasiCompact (f : X ⟶ S)
    (D : (qcSeparatedProperty f).FullSubcategory) :
    QuasiCompact ((D.obj).obj.obj PUnit.unit).hom := sorry

/-- A selected étale descent datum has separated component morphism. -/
instance isSeparated (f : X ⟶ S)
    (D : (qcSeparatedProperty f).FullSubcategory) :
    IsSeparated ((D.obj).obj.obj PUnit.unit).hom := sorry

end qcSeparatedProperty

namespace canonicalFunctor

/-- The canonical étale descent functor preserves quasi-compactness and separatedness. -/
theorem qcSeparated_mapsTo (f : X ⟶ S) :
    Scheme.Etale.qcSeparatedProperty S ≤
      (qcSeparatedProperty f).inverseImage (canonicalFunctor f) := sorry

/-- The canonical étale descent functor restricted to quasi-compact separated objects. -/
noncomputable def qcSeparated (f : X ⟶ S) :
    (Scheme.Etale.qcSeparatedProperty S).FullSubcategory ⥤
      (qcSeparatedProperty f).FullSubcategory :=
  ObjectProperty.FullSubcategory.restrict
    (canonicalFunctor f) (qcSeparated_mapsTo f)

/-- The underlying étale descent datum of `qcSeparated f` on an object is the value of
the unrestricted canonical functor. -/
theorem qcSeparated_obj_obj (f : X ⟶ S)
    (U : (Scheme.Etale.qcSeparatedProperty S).FullSubcategory) :
    ((qcSeparated f).obj U).obj = (canonicalFunctor f).obj U.obj := sorry

end canonicalFunctor

end Scheme.DescentData.Etale
end AlgebraicGeometry
