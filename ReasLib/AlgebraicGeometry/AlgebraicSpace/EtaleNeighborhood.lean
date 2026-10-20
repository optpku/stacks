module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.AlgebraicGeometry.Scheme.FieldValuedPoint
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Presentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Comparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology

/-!
# Étale neighbourhoods of a point of an algebraic space

An étale neighbourhood of a point `x` of an algebraic space `X` is an étale morphism from a
scheme into `X` together with a selected point lying over `x`. It is elementary when the
induced residue-field morphism `Spec(κ(u)) ⟶ X` is a monomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace EtaleNeighborhood

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- A morphism of small étale site objects sends a scheme point over `x` to a scheme point
over `x`. -/
theorem pointFiber_map_mem {x : Points X} {U V : smallEtaleSite X} (f : U ⟶ V)
    (u : U.left.left) (hu : Points.mapOfOver U.hom u = x) :
    Points.mapOfOver V.hom (f.left.left u) = x :=
  sorry

/-- The functor sending an object `U` of the small étale site of `X` to the type of points of
the underlying scheme lying over a fixed point `x` of `X`. -/
def pointFiber (x : Points X) : smallEtaleSite X ⥤ Type u where
  obj U := {u : U.left.left // Points.mapOfOver U.hom u = x}
  map {U V} (f : U ⟶ V) :=
    TypeCat.ofHom fun (p : {u : U.left.left // Points.mapOfOver U.hom u = x}) ↦
      ⟨f.left.left p.1, pointFiber_map_mem f p.1 p.2⟩
  map_id := by
    intro U
    apply ConcreteCategory.hom_ext
    intro p
    apply Subtype.ext
    rfl
  map_comp := by
    intro U V W f g
    apply ConcreteCategory.hom_ext
    intro p
    apply Subtype.ext
    rfl

/-- The value of `pointFiber x` at `U` is the type of points of `U` lying over `x`. -/
theorem pointFiber_obj (x : Points X) (U : smallEtaleSite X) :
    (pointFiber x).obj U = {u : U.left.left // Points.mapOfOver U.hom u = x} :=
  sorry

end EtaleNeighborhood

/-- An étale neighbourhood of a point `x` of an algebraic space `X` is an étale `X`-scheme
together with a selected point lying over `x`. -/
abbrev EtaleNeighborhood {S : Scheme.{u}} (X : AlgebraicSpace S) (x : Points X) :=
  (EtaleNeighborhood.pointFiber x).Elements

namespace EtaleNeighborhood

variable {S : Scheme.{u}} {X : AlgebraicSpace S} {x : Points X}

/-- The object of the small étale site underlying an étale neighbourhood. -/
abbrev toSite (U : EtaleNeighborhood X x) : smallEtaleSite X :=
  U.1

/-- The underlying scheme over `S` of an étale neighbourhood. -/
abbrev toOver (U : EtaleNeighborhood X x) : Over S :=
  U.toSite.left

/-- The underlying scheme of an étale neighbourhood. -/
abbrev scheme (U : EtaleNeighborhood X x) : Scheme.{u} :=
  U.toOver.left

/-- The structure morphism of an étale neighbourhood, as an étale morphism of algebraic
spaces into `X`. -/
abbrev hom (U : EtaleNeighborhood X x) : ofOver U.toOver ⟶ X :=
  U.toSite.hom

/-- The selected point of an étale neighbourhood. -/
abbrev point (U : EtaleNeighborhood X x) : U.scheme :=
  U.2.1

/-- The selected point of an étale neighbourhood maps to the specified point of `X`. -/
theorem map_point (U : EtaleNeighborhood X x) :
    Points.mapOfOver U.hom U.point = x :=
  sorry

/-- Construct an étale neighbourhood from an object of the small étale site and a point over
`x`. -/
def of (U : smallEtaleSite X) (u : U.left.left) (hu : Points.mapOfOver U.hom u = x) :
    EtaleNeighborhood X x :=
  Functor.elementsMk (pointFiber x) U ⟨u, hu⟩

/-- An étale neighbourhood is an étale morphism from a scheme together with a selected point
over `x`. -/
theorem spec (U : EtaleNeighborhood X x) :
    Etale U.hom ∧ Points.mapOfOver U.hom U.point = x :=
  sorry

/-- The underlying site object of `of U u hu` is `U`. -/
@[simp]
theorem of_toSite (U : smallEtaleSite X) (u : U.left.left)
    (hu : Points.mapOfOver U.hom u = x) : (of U u hu).toSite = U :=
  sorry

/-- The selected point of `of U u hu` is the supplied point. -/
@[simp]
theorem of_point (U : smallEtaleSite X) (u : U.left.left)
    (hu : Points.mapOfOver U.hom u = x) : (of U u hu).point = u :=
  sorry

/-- The canonical field-valued point `Spec(κ(u)) ⟶ X` of an étale neighbourhood. -/
def residuePoint (U : EtaleNeighborhood X x) : FieldValuedPoint X :=
  (FieldValuedPoint.ofScheme (Scheme.FieldValuedPoint.residuePoint U.point)).map U.hom

/-- The morphism `Spec(κ(u)) ⟶ X` of an étale neighbourhood. -/
abbrev residueHom (U : EtaleNeighborhood X x) :=
  (residuePoint U).hom

/-- The morphism of `residuePoint U` is `residueHom U`. -/
theorem residuePoint_hom (U : EtaleNeighborhood X x) :
    (residuePoint U).hom = residueHom U :=
  sorry

/-- The residue-field point of an étale neighbourhood represents the selected point `x`. -/
theorem residuePoint_mk (U : EtaleNeighborhood X x) :
    Points.mk (residuePoint U) = x :=
  sorry

/-- An étale neighbourhood is elementary when `Spec(κ(u)) ⟶ X` is a monomorphism. -/
def IsElementary (U : EtaleNeighborhood X x) : Prop :=
  Mono (residueHom U)

/-- The monomorphism characterization of an elementary étale neighbourhood. -/
theorem isElementary_iff (U : EtaleNeighborhood X x) :
    U.IsElementary ↔ Mono (residueHom U) :=
  sorry

/-- The full subcategory of elementary étale neighbourhoods of the pointed algebraic space
`(X, x)`. -/
abbrev Elementary (X : AlgebraicSpace S) (x : Points X) :=
  ObjectProperty.FullSubcategory fun U : EtaleNeighborhood X x ↦ U.IsElementary

namespace Elementary

/-- Regard an elementary étale neighbourhood as an object of the elementary full
subcategory. -/
def of (U : EtaleNeighborhood X x) (hU : U.IsElementary) : Elementary X x where
  obj := U
  property := hU

/-- An object of the elementary full subcategory is an elementary étale neighbourhood. -/
theorem isElementary (U : Elementary X x) : U.obj.IsElementary :=
  sorry

/-- The underlying étale neighbourhood of `of U hU` is `U`. -/
@[simp]
theorem of_obj (U : EtaleNeighborhood X x) (hU : U.IsElementary) :
    (of U hU).obj = U :=
  sorry

/-- An elementary étale neighbourhood is an étale scheme morphism to `X` with selected point
over `x` whose residue-field morphism is a monomorphism. -/
theorem spec (U : Elementary X x) :
    Etale U.obj.hom ∧ Points.mapOfOver U.obj.hom U.obj.point = x ∧
      Mono (residueHom U.obj) :=
  sorry

/-- A morphism of elementary étale neighbourhoods is a morphism in the elementary full
subcategory. -/
abbrev Hom (U V : Elementary X x) :=
  U ⟶ V

namespace Hom

/-- The morphism of étale neighbourhoods underlying a morphism of elementary étale
neighbourhoods. -/
abbrev toNeighborhoodHom {U V : Elementary X x} (f : Hom U V) : U.obj ⟶ V.obj :=
  f.hom

/-- The morphism of small étale site objects underlying a morphism of elementary étale
neighbourhoods. -/
abbrev toSiteHom {U V : Elementary X x} (f : Hom U V) : U.obj.toSite ⟶ V.obj.toSite :=
  f.toNeighborhoodHom.val

/-- The morphism of schemes over `S` underlying a morphism of elementary étale
neighbourhoods. -/
abbrev overHom {U V : Elementary X x} (f : Hom U V) : U.obj.toOver ⟶ V.obj.toOver :=
  f.toSiteHom.left

/-- The scheme morphism underlying a morphism of elementary étale neighbourhoods. -/
abbrev schemeHom {U V : Elementary X x} (f : Hom U V) : U.obj.scheme ⟶ V.obj.scheme :=
  f.overHom.left

/-- A morphism of elementary étale neighbourhoods preserves the selected points. -/
theorem map_point {U V : Elementary X x} (f : Hom U V) :
    f.schemeHom U.obj.point = V.obj.point :=
  sorry

/-- A morphism of elementary étale neighbourhoods is a morphism over `X`. -/
theorem over_fac {U V : Elementary X x} (f : Hom U V) :
    ofOverMap f.overHom ≫ V.obj.hom = U.obj.hom :=
  sorry

/-- Construct a morphism of elementary étale neighbourhoods from a morphism of the underlying
étale neighbourhoods. -/
def of {U V : Elementary X x} (f : U.obj ⟶ V.obj) : Hom U V :=
  ObjectProperty.homMk f

/-- A morphism of elementary étale neighbourhoods is a morphism over `X` sending the selected
point to the selected point. -/
theorem spec {U V : Elementary X x} (f : Hom U V) :
    ofOverMap f.overHom ≫ V.obj.hom = U.obj.hom ∧
      f.schemeHom U.obj.point = V.obj.point :=
  sorry

end Hom

end Elementary

/-- A morphism of étale neighbourhoods is a morphism in the category of elements of the
point-fibre functor. -/
abbrev Hom (U V : EtaleNeighborhood X x) :=
  U ⟶ V

namespace Hom

/-- The morphism of small étale site objects underlying a morphism of étale neighbourhoods. -/
abbrev toSiteHom {U V : EtaleNeighborhood X x} (f : Hom U V) : U.toSite ⟶ V.toSite :=
  f.val

/-- The morphism of schemes over `S` underlying a morphism of étale neighbourhoods. -/
abbrev overHom {U V : EtaleNeighborhood X x} (f : Hom U V) : U.toOver ⟶ V.toOver :=
  f.toSiteHom.left

/-- The scheme morphism underlying a morphism of étale neighbourhoods. -/
abbrev schemeHom {U V : EtaleNeighborhood X x} (f : Hom U V) : U.scheme ⟶ V.scheme :=
  f.overHom.left

/-- A morphism of étale neighbourhoods preserves the selected points. -/
theorem map_point {U V : EtaleNeighborhood X x} (f : Hom U V) :
    f.schemeHom U.point = V.point :=
  sorry

/-- A morphism of étale neighbourhoods is a morphism over `X`. -/
theorem over_fac {U V : EtaleNeighborhood X x} (f : Hom U V) :
    ofOverMap f.overHom ≫ V.hom = U.hom :=
  sorry

/-- Construct a morphism of étale neighbourhoods from a pointed morphism of small étale site
objects. -/
def of {U V : EtaleNeighborhood X x} (f : U.toSite ⟶ V.toSite)
    (hf : f.left.left U.point = V.point) : Hom U V :=
  CategoryOfElements.homMk U V f (Subtype.ext hf)

/-- A morphism of étale neighbourhoods is a morphism over `X` sending the selected point to
the selected point. -/
theorem spec {U V : EtaleNeighborhood X x} (f : Hom U V) :
    ofOverMap f.overHom ≫ V.hom = U.hom ∧ f.schemeHom U.point = V.point :=
  sorry

end Hom

end EtaleNeighborhood

end AlgebraicGeometry.AlgebraicSpace
