/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.CategoryTheory.Functor.TypeValuedFlat
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/-- An étale neighbourhood of a point `s : S` is an étale `S`-scheme together with a
selected point lying over `s`. -/
abbrev EtaleNeighborhood (S : Scheme.{u}) (s : S) :=
  (Etale.forget S ⋙ FunctorToTypes.fromOverFunctor Scheme.forget s).Elements

namespace EtaleNeighborhood

/-- The étale `S`-scheme underlying an étale neighbourhood. -/
abbrev toEtale {S : Scheme.{u}} {s : S} (U : EtaleNeighborhood S s) : S.Etale := U.1

/-- The selected point of an étale neighbourhood. -/
abbrev point {S : Scheme.{u}} {s : S} (U : EtaleNeighborhood S s) : U.toEtale.left := U.2.1

/-- The selected point of an étale neighbourhood maps to the specified base point. -/
theorem map_point {S : Scheme.{u}} {s : S} (U : EtaleNeighborhood S s) :
    U.toEtale.hom U.point = s :=
  (FunctorToTypes.mem_fromOverSubfunctor_iff Scheme.forget s U.point).1 U.2.2

/-- Construct an étale neighbourhood from an étale `S`-scheme and a point over `s`. -/
def of {S : Scheme.{u}} {s : S} (U : S.Etale) (u : U.left)
    (hu : U.hom u = s) : EtaleNeighborhood S s :=
  Functor.elementsMk _ U
    ⟨u, (FunctorToTypes.mem_fromOverSubfunctor_iff Scheme.forget s u).2 hu⟩

/-- An étale neighbourhood carries both étaleness and its defining point equation. -/
theorem spec {S : Scheme.{u}} {s : S} (U : EtaleNeighborhood S s) :
    AlgebraicGeometry.Etale U.toEtale.hom ∧ U.toEtale.hom U.point = s := sorry

/-- A morphism of étale neighbourhoods is a morphism in the category of elements of the
point-fibre functor. -/
abbrev Hom {S : Scheme.{u}} {s : S} (V U : EtaleNeighborhood S s) := V ⟶ U

namespace Hom

/-- The morphism of étale `S`-schemes underlying a morphism of étale neighbourhoods. -/
abbrev toEtaleHom {S : Scheme.{u}} {s : S} {V U : EtaleNeighborhood S s}
    (f : Hom V U) : V.toEtale ⟶ U.toEtale := f.val

/-- The underlying scheme morphism preserves the selected points. -/
theorem map_point {S : Scheme.{u}} {s : S} {V U : EtaleNeighborhood S s} (f : Hom V U) :
    f.toEtaleHom.left V.point = U.point := congrArg Subtype.val f.property

/-- Construct a morphism of étale neighbourhoods from a pointed morphism of étale
`S`-schemes. -/
def of {S : Scheme.{u}} {s : S} {V U : EtaleNeighborhood S s}
    (f : V.toEtale ⟶ U.toEtale) (hf : f.left V.point = U.point) : Hom V U :=
  CategoryOfElements.homMk V U f (Subtype.ext hf)

/-- A morphism of étale neighbourhoods preserves the selected point and commutes with
the structure morphisms to the base scheme. -/
theorem spec {S : Scheme.{u}} {s : S} {V U : EtaleNeighborhood S s} (f : Hom V U) :
    f.toEtaleHom.left V.point = U.point ∧
      f.toEtaleHom.left ≫ U.toEtale.hom = V.toEtale.hom := sorry

end Hom

/-- An étale neighbourhood is elementary when its structural morphism induces an
isomorphism on residue fields at the selected point. -/
def IsElementary {S : Scheme.{u}} {s : S} (U : EtaleNeighborhood S s) : Prop :=
  IsIso (U.toEtale.hom.residueFieldMap U.point)

/-- The canonical residue-field-map characterization of an elementary étale
neighbourhood. -/
theorem isElementary_iff {S : Scheme.{u}} {s : S} (U : EtaleNeighborhood S s) :
    U.IsElementary ↔ IsIso (U.toEtale.hom.residueFieldMap U.point) := sorry

/-- The full subcategory of elementary étale neighbourhoods of the pointed scheme `(S, s)`. -/
abbrev Elementary (S : Scheme.{u}) (s : S) :=
  ObjectProperty.FullSubcategory (fun U : EtaleNeighborhood S s ↦ U.IsElementary)

namespace Elementary

/-- Regard an elementary étale neighbourhood as an object of the elementary full
subcategory. -/
def of {S : Scheme.{u}} {s : S} (U : EtaleNeighborhood S s) (hU : U.IsElementary) :
    Elementary S s where
  obj := U
  property := hU

/-- An object of the elementary full subcategory is an elementary étale neighbourhood. -/
theorem isElementary {S : Scheme.{u}} {s : S} (U : Elementary S s) :
    U.obj.IsElementary := sorry

/-- The underlying étale neighbourhood of `of U hU` is `U`. -/
@[simp]
theorem of_obj {S : Scheme.{u}} {s : S} (U : EtaleNeighborhood S s)
    (hU : U.IsElementary) : (of U hU).obj = U := sorry

end Elementary

end EtaleNeighborhood

end AlgebraicGeometry.Scheme
