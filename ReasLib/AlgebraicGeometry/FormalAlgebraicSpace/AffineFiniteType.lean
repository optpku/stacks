module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.FormalSpectrum.Morphism
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.AffinePresentation
public import ReasLib.Topology.Algebra.Ring.Taut
public import ReasLib.RingTheory.Topology.FiniteType
public import ReasLib.RingTheory.Topology.CountablyIndexed

/-!
# Finite type morphisms of affine formal algebraic spaces

For an affine formal algebraic space with countably indexed target, local
finite type and finite type are characterized by compatible formal-spectrum
presentations and a taut topologically finite-type map of rings.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.FormalAlgebraicSpace

universe u

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

variable {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}

/-- A morphism `f : X ⟶ Y` of functors of points over `S` corresponds to a
continuous arrow `φ : B →+* A` of countably indexed weakly admissible rings
that is taut and topologically of finite type, via identifications of `X` and
`Y` with the underlying functors of `spf A hA` and `spf B hB`. -/
def exists_spfMap_isTaut_and_topologicallyOfFiniteType
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)] (f : X ⟶ Y) : Prop :=
  ∃ (A B : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
    (_ : TopologicalRing.IsWeaklyAdmissibleRing A)
    (_ : TopologicalRing.IsCountablyIndexed A) (_ : CommRing B)
    (_ : TopologicalSpace B) (_ : TopologicalRing.IsWeaklyAdmissibleRing B)
    (_ : TopologicalRing.IsCountablyIndexed B) (hA : Spec (.of A) ⟶ S)
    (hB : Spec (.of B) ⟶ S) (φ : B →+* A) (hφ : Continuous φ)
    (h_over : Spec.map (CommRingCat.ofHom φ) ≫ hB = hA)
    (eX : (sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).obj (spf A hA) ≅ X)
    (eY : (sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).obj (spf B hB) ≅ Y),
    (φ.IsTaut ∧ φ.TopologicallyOfFiniteType) ∧
      eX.hom ≫ f =
        (sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).map
            (spfMap φ hφ h_over) ≫ eY.hom

/-- A continuous taut topologically finite-type `WAdm^count` arrow, together
with `Spf` identifications of the source and target, witnesses the
correspondence predicate. -/
theorem exists_spfMap_isTaut_and_topologicallyOfFiniteType_of
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)] {f : X ⟶ Y}
    {A B : Type u} [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsWeaklyAdmissibleRing A]
    [TopologicalRing.IsCountablyIndexed A] [CommRing B] [TopologicalSpace B]
    [TopologicalRing.IsWeaklyAdmissibleRing B]
    [TopologicalRing.IsCountablyIndexed B] (hA : Spec (.of A) ⟶ S)
    (hB : Spec (.of B) ⟶ S) (φ : B →+* A) (hφ : Continuous φ)
    (h_over : Spec.map (CommRingCat.ofHom φ) ≫ hB = hA)
    (eX : (sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).obj (spf A hA) ≅ X)
    (eY : (sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).obj (spf B hB) ≅ Y)
    (hφ_tfae : φ.IsTaut ∧ φ.TopologicallyOfFiniteType)
    (h_map : eX.hom ≫ f =
      (sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).map
          (spfMap φ hφ h_over) ≫ eY.hom) :
    exists_spfMap_isTaut_and_topologicallyOfFiniteType f :=
  ⟨A, B, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance,
    hA, hB, φ, hφ, h_over, eX, eY, hφ_tfae, h_map⟩

/-- The correspondence predicate supplies countably indexed weakly admissible
presentations and a continuous taut topologically finite-type arrow inducing
`f` via `spfMap`. -/
theorem exists_spfMap_isTaut_and_topologicallyOfFiniteType_spec
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)] {f : X ⟶ Y}
    (h : exists_spfMap_isTaut_and_topologicallyOfFiniteType f) :
    ∃ (A B : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
      (_ : TopologicalRing.IsWeaklyAdmissibleRing A)
      (_ : TopologicalRing.IsCountablyIndexed A) (_ : CommRing B)
      (_ : TopologicalSpace B) (_ : TopologicalRing.IsWeaklyAdmissibleRing B)
      (_ : TopologicalRing.IsCountablyIndexed B) (hA : Spec (.of A) ⟶ S)
      (hB : Spec (.of B) ⟶ S) (φ : B →+* A) (hφ : Continuous φ)
      (h_over : Spec.map (CommRingCat.ofHom φ) ≫ hB = hA)
      (eX : (sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).obj
          (spf A hA) ≅ X)
      (eY : (sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).obj
          (spf B hB) ≅ Y),
      (φ.IsTaut ∧ φ.TopologicallyOfFiniteType) ∧
        eX.hom ≫ f =
          (sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).map
              (spfMap φ hφ h_over) ≫ eY.hom :=
  h

/-- For a morphism of affine formal algebraic spaces, locally of finite type
is equivalent to of finite type. -/
theorem locallyOfFiniteType_iff_finiteType [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) : FormalAlgebraicSpace.LocallyOfFiniteType f ↔ FiniteType f :=
  sorry

/-- An affine morphism of functors of points that is locally of finite type is
of finite type. -/
instance instFiniteType_of_locallyOfFiniteType [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) [FormalAlgebraicSpace.LocallyOfFiniteType f] : FiniteType f :=
  (locallyOfFiniteType_iff_finiteType f).mp inferInstance

/-- For a morphism of affine formal algebraic spaces with countably indexed
 target, local finite type, finite type, and correspondence to a continuous
 taut topologically finite-type map of countably indexed weakly admissible
 rings are equivalent. -/
theorem locallyOfFiniteType_tfae [IsAffine X] [IsCountablyIndexedAffine Y]
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)] (f : X ⟶ Y) :
    List.TFAE [FormalAlgebraicSpace.LocallyOfFiniteType f, FiniteType f,
      exists_spfMap_isTaut_and_topologicallyOfFiniteType f] :=
  sorry

/-- For a morphism of affine formal algebraic spaces with countably indexed
target, locally of finite type is equivalent to corresponding to a taut
topologically finite-type arrow of `WAdm^count`. -/
theorem locallyOfFiniteType_iff_exists_spfMap
    [IsAffine X] [IsCountablyIndexedAffine Y]
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)] (f : X ⟶ Y) :
    FormalAlgebraicSpace.LocallyOfFiniteType f ↔ exists_spfMap_isTaut_and_topologicallyOfFiniteType f :=
  (locallyOfFiniteType_tfae f).out 0 2

/-- For a morphism of affine formal algebraic spaces with countably indexed
target, of finite type is equivalent to corresponding to a taut topologically
finite-type arrow of `WAdm^count`. -/
theorem finiteType_iff_exists_spfMap
    [IsAffine X] [IsCountablyIndexedAffine Y]
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)] (f : X ⟶ Y) :
    FiniteType f ↔ exists_spfMap_isTaut_and_topologicallyOfFiniteType f :=
  (locallyOfFiniteType_tfae f).out 1 2

end AlgebraicGeometry.AffineFormalAlgebraicSpace
