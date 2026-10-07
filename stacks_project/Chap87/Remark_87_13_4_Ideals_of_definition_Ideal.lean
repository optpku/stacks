module

public import Mathlib.RingTheory.Ideal.Basic
public import ReasLib.RingTheory.Topology.Adic.Complete
public import stacks_project.Chap87.Lemma_87_2_1_Size
public import stacks_project.Chap87.Remark_87_9_8_Affine
public import stacks_project.Chap87.«87_2_0_1_Spf»

/-!
# Ideals of definition on EGA formal schemes

An ideal sheaf on an EGA formal scheme is recorded by its values on formal
affine opens, with the restriction-compatibility of an ideal sheaf. It is an
ideal of definition when those values are ideals of definition of the
admissible section rings.
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory Opposite TopologicalSpace Topology AlgebraicGeometry
open AlgebraicGeometry.Spec (structureSheaf)
open TopologicalRing

namespace AlgebraicGeometry.FormalScheme

/-- Sections of the structure sheaf of an EGA formal scheme over an open. -/
abbrev sections (X : FormalScheme.{u}) (U : Opens X.carrier) : Type u :=
  X.presheaf.obj (op U)

/-- Unfolding of `sections`. -/
theorem sections_eq (X : FormalScheme.{u}) (U : Opens X.carrier) :
    sections X U = X.presheaf.obj (op U) :=
  sorry

/-- Affine formal opens of an EGA formal scheme have admissible section rings. -/
instance instIsAdmissibleRing_sections {X : FormalScheme.{u}} (U : X.affineOpens) :
    IsAdmissibleRing (X.presheaf.obj (op U.1) : Type u) :=
  sorry

/-- An ideal sheaf on an EGA formal scheme, recorded by its ideals of sections
on formal affine opens together with restriction compatibility. -/
structure IdealSheafData (X : FormalScheme.{u}) where
  /-- The component of the ideal sheaf at a formal affine open. -/
  ideal : ∀ U : X.affineOpens, Ideal (X.presheaf.obj (op U.1) : Type u)
  /-- Restriction of a larger affine-open component lands in the smaller one. -/
  map_ideal :
    ∀ {U V : X.affineOpens} (h : U.1 ≤ V.1),
      (ideal V).map (X.presheaf.map (homOfLE h).op).val ≤ ideal U

/-- Construct ideal-sheaf data from an affine-open family of ideals together
with the restriction-compatibility of an ideal sheaf. -/
def IdealSheafData.of {X : FormalScheme.{u}}
    (ideal : ∀ U : X.affineOpens, Ideal (X.presheaf.obj (op U.1) : Type u))
    (map_ideal :
      ∀ {U V : X.affineOpens} (h : U.1 ≤ V.1),
        (ideal V).map (X.presheaf.map (homOfLE h).op).val ≤ ideal U) :
    IdealSheafData X where
  ideal := ideal
  map_ideal := map_ideal

/-- The smart constructor recovers the given affine-open family of ideals. -/
theorem IdealSheafData.of_spec {X : FormalScheme.{u}}
    (ideal : ∀ U : X.affineOpens, Ideal (X.presheaf.obj (op U.1) : Type u))
    (map_ideal :
      ∀ {U V : X.affineOpens} (h : U.1 ≤ V.1),
        (ideal V).map (X.presheaf.map (homOfLE h).op).val ≤ ideal U) :
    (IdealSheafData.of ideal map_ideal).ideal = ideal :=
  sorry

/-- Restriction compatibility of an ideal sheaf on formal affine opens. -/
theorem IdealSheafData.map_ideal_apply {X : FormalScheme.{u}} (I : IdealSheafData X)
    {U V : X.affineOpens} (h : U.1 ≤ V.1) :
    (I.ideal V).map (X.presheaf.map (homOfLE h).op).val ≤ I.ideal U :=
  sorry

/-- Canonical map from an admissible ring into sections of `ofSpf A` over an
open of its formal spectrum. -/
def ofSpfSectionHom (A : TopCommRingCat.{u}) (hA : IsAdmissibleRing A)
    (U : Opens (FormalScheme.ofSpf A hA).carrier) :
    (A : Type u) →+* ((FormalScheme.ofSpf A hA).presheaf.obj (op U) : Type u) where
  toFun a :=
    ⟨fun I hI ↦
      algebraMap (A ⧸ I)
        (((structureSheaf (A ⧸ I)).1.obj
            (op (pullbackOpens
              (U : Opens (AlgebraicGeometry.OpenPrime (A : Type u))) I hI))) : Type u)
        (Ideal.Quotient.mk I a),
      sorry⟩
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

/-- Components of `ofSpfSectionHom` are the structure-sheaf algebra maps of
`A ⧸ I`. -/
theorem ofSpfSectionHom_component (A : TopCommRingCat.{u}) (hA : IsAdmissibleRing A)
    (U : Opens (FormalScheme.ofSpf A hA).carrier) (a : A) (I : Ideal (A : Type u))
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) :
    (ofSpfSectionHom A hA U a).component I hI =
      algebraMap (A ⧸ I)
        (((structureSheaf (A ⧸ I)).1.obj
            (op (pullbackOpens
              (U : Opens (AlgebraicGeometry.OpenPrime (A : Type u))) I hI))) : Type u)
        (Ideal.Quotient.mk I a) :=
  sorry

end AlgebraicGeometry.FormalScheme

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

/-- An ideal of definition, bundled as an index for affine formal spectra. -/
structure IdealOfDefinition (A : Type u) [CommRing A] [TopologicalSpace A] where
  /-- Underlying ideal. -/
  ideal : Ideal A
  /-- The ideal is an ideal of definition. -/
  isIdeal : TopologicalRing.Ideal.IsIdealOfDefinition ideal

/-- Bundle an ideal with a proof that it is an ideal of definition. -/
def IdealOfDefinition.of {A : Type u} [CommRing A] [TopologicalSpace A] (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) : IdealOfDefinition A where
  ideal := I
  isIdeal := hI

/-- The smart constructor recovers the underlying ideal and the ideal-of-definition
property. -/
theorem IdealOfDefinition.of_spec {A : Type u} [CommRing A] [TopologicalSpace A]
    (I : Ideal A) (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) :
    (IdealOfDefinition.of I hI).ideal = I ∧
      TopologicalRing.Ideal.IsIdealOfDefinition (IdealOfDefinition.of I hI).ideal :=
  sorry

end AlgebraicGeometry.AffineFormalAlgebraicSpace

namespace AlgebraicGeometry.FormalScheme

/-- The ideal sheaf on `ofSpf A` extending an ideal of the admissible ring `A`. -/
def IdealSheafData.ofSpf (A : TopCommRingCat.{u}) (hA : IsAdmissibleRing A)
    (I : Ideal (A : Type u)) : IdealSheafData (FormalScheme.ofSpf A hA) where
  ideal U := I.map (ofSpfSectionHom A hA U.1)
  map_ideal := sorry

/-- On affine opens of `ofSpf A`, `ofSpf` is the extension of the given ideal
along `ofSpfSectionHom`. -/
theorem IdealSheafData.ofSpf_ideal (A : TopCommRingCat.{u}) (hA : IsAdmissibleRing A)
    (I : Ideal (A : Type u)) (U : (FormalScheme.ofSpf A hA).affineOpens) :
    (IdealSheafData.ofSpf A hA I).ideal U = I.map (ofSpfSectionHom A hA U.1) :=
  sorry

/-- The kernel ideal sheaf of a morphism of EGA formal schemes, recorded on
formal affine opens of the target. -/
def IdealSheafData.ker {Y X : FormalScheme.{u}} (f : Y ⟶ X) : IdealSheafData X where
  ideal U := RingHom.ker (f.toLTRSHom.toSheafedHom.hom.c.app (op U.1)).val
  map_ideal := sorry

/-- On a formal affine open, `ker f` is the kernel of the component ring
homomorphism of `f`. -/
theorem IdealSheafData.ker_spec {Y X : FormalScheme.{u}} (f : Y ⟶ X)
    (U : X.affineOpens) :
    (IdealSheafData.ker f).ideal U =
      RingHom.ker (f.toLTRSHom.toSheafedHom.hom.c.app (op U.1)).val :=
  sorry

/-- An ideal sheaf is an ideal of definition when its sections on every formal
affine open are an ideal of definition. -/
class IsIdealOfDefinition {X : FormalScheme.{u}} (I : IdealSheafData X) : Prop where
  /-- Affine-open sections form an ideal of definition. -/
  isIdeal :
    ∀ U : X.affineOpens, TopologicalRing.Ideal.IsIdealOfDefinition (I.ideal U)

/-- Unfolding of `IsIdealOfDefinition`. -/
theorem isIdealOfDefinition_iff {X : FormalScheme.{u}} (I : IdealSheafData X) :
    IsIdealOfDefinition I ↔
      ∀ U : X.affineOpens, TopologicalRing.Ideal.IsIdealOfDefinition (I.ideal U) :=
  sorry

/-- Being an ideal of definition may be checked on the members of an affine
open covering. -/
theorem isIdealOfDefinition_iff_affineCover {X : FormalScheme.{u}}
    (I : IdealSheafData X) {ι : Type u} (𝒰 : ι → X.affineOpens)
    (hcover : ⨆ i, (𝒰 i).1 = ⊤) :
    IsIdealOfDefinition I ↔
      ∀ i, TopologicalRing.Ideal.IsIdealOfDefinition (I.ideal (𝒰 i)) :=
  sorry

/-- The ideal sheaf on `ofSpf A` extending an ideal of definition of `A` is an
ideal of definition. -/
instance instIsIdealOfDefinition_ofSpf (A : TopCommRingCat.{u})
    (hA : IsAdmissibleRing A)
    (I : AffineFormalAlgebraicSpace.IdealOfDefinition A) :
    IsIdealOfDefinition (IdealSheafData.ofSpf A hA I.ideal) :=
  sorry

end AlgebraicGeometry.FormalScheme

namespace TopologicalRing.Ideal

/-- In an admissible topological ring, every open ideal contained in an ideal
of definition is itself an ideal of definition. -/
theorem isIdealOfDefinition_of_le_isOpen {A : Type u} [CommRing A]
    [TopologicalSpace A] [IsAdmissibleRing A] {I J : Ideal A}
    (hI : IsIdealOfDefinition I) (hJ : IsOpen (J : Set A)) (hJI : J ≤ I) :
    IsIdealOfDefinition J :=
  sorry

end TopologicalRing.Ideal
