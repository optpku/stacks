module

public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.Dimension
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Unramified
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite
public import ReasLib.AlgebraicGeometry.Scheme.Normal
public import ReasLib.RingTheory.Excellent

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Hom.FiniteType
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- For a flat morphism of locally Noetherian schemes, finite-type
quasi-finiteness at a non-generic point and unramifiedness at every
one-dimensional specialization imply étaleness at that point. -/
theorem etaleAt_of_purity_branchLocus
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [Flat f]
    (x : X)
    (h_qf : FiniteType.QuasiFiniteAt f x)
    (h_not_generic : x ∉ genericPoints X)
    (h_unramified :
      ∀ x' : X, x' ⤳ x →
        ringKrullDim (X.presheaf.stalk x') = 1 →
          f.UnramifiedAt x') :
    f.EtaleAt x := sorry

/-- A finite type morphism to the spectrum of an excellent regular local ring is
étale at a point with normal two-dimensional stalk when it is étale away from
the closure of that point. -/
theorem etaleAt_of_purity
    (A : Type u) [CommRing A] [IsExcellentRing A] [IsRegularLocalRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    [Scheme.Hom.FiniteType f]
    (x : X) (h_normal : X.isNormalAt x)
    (h_dimension : ringKrullDim (X.presheaf.stalk x) = 2)
    (h_etale_off_closure :
      ∀ y : X, y ∉ closure ({x} : Set X) → f.EtaleAt y) :
    f.EtaleAt x := sorry

/-- A morphism of locally Noetherian schemes is étale at a point with normal stalk
and regular image stalk if it is quasi-finite there, the two stalks have equal
positive Krull dimension, and it is unramified at every one-dimensional
specialization of that point. -/
theorem etaleAt_of_unramifiedAt_codimOne_specializations
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (x : X) (hX : X.isNormalAt x)
    (hY : IsRegularLocalRing (Y.presheaf.stalk (f.base x)))
    (hqf : f.QuasiFiniteAt x)
    (hdim : ringKrullDim (X.presheaf.stalk x) = ringKrullDim (Y.presheaf.stalk (f.base x)))
    (hpos : 1 ≤ ringKrullDim (X.presheaf.stalk x))
    (hunr : ∀ x' : X, x' ⤳ x → ringKrullDim (X.presheaf.stalk x') = 1 → f.UnramifiedAt x') :
    f.EtaleAt x := sorry

/-- A locally finite type morphism of locally Noetherian schemes is étale at a
point with normal source stalk of positive Krull dimension and regular target
stalk when it is étale at every one-dimensional specialization of that point. -/
theorem etaleAt_of_etaleAt_codimOne_specializations
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [LocallyOfFiniteType f] (x : X) (hX : X.isNormalAt x)
    (hY : IsRegularLocalRing (Y.presheaf.stalk (f.base x)))
    (hpos : 1 ≤ ringKrullDim (X.presheaf.stalk x))
    (hetale : ∀ x' : X, x' ⤳ x → ringKrullDim (X.presheaf.stalk x') = 1 → f.EtaleAt x') :
    f.EtaleAt x := sorry

end AlgebraicGeometry.Scheme.Hom
