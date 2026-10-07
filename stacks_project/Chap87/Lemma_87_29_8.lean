module

public import Mathlib.Data.List.TFAE
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Definition_87_5_1_Taut
public import stacks_project.Chap87.Definition_87_29_1_TopologicallyOfFiniteType
public import stacks_project.Chap87.Lemma_87_9_10_Map
public import stacks_project.Chap87.Lemma_87_24_4_FiniteType
public import stacks_project.Chap87.Lemma_87_37_6_CountablyIndexed
public import stacks_project.Chap87.«87_21_2_1_LocalizeSquare»

/-!
# Affine finite type morphisms versus WAdm^count arrows

For a morphism of affine formal algebraic spaces whose target is countably
indexed, being locally of finite type, being of finite type, and corresponding
to a taut topologically finite-type arrow of `WAdm^count` are equivalent.
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

/-- Correspondence with a taut topologically finite-type `WAdm^count` arrow is
the existence of countably indexed weakly admissible presentations of `X` and
`Y` and a continuous `φ : B →+* A` identified with `f` via `spfMap`. -/
theorem exists_spfMap_isTaut_and_topologicallyOfFiniteType_iff
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)] (f : X ⟶ Y) :
    exists_spfMap_isTaut_and_topologicallyOfFiniteType f ↔
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
  sorry

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
  sorry

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
  sorry

/-- Lemma 87.29.8: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
affine formal algebraic spaces. Assume `Y` is countably indexed. The following
are equivalent: `f` is locally of finite type, `f` is of finite type, and `f`
corresponds to a morphism `B →+* A` of `WAdm^count` satisfying the equivalent
conditions of Lemma 87.29.6. -/
@[stacks 0ANV]
theorem locallyOfFiniteType_tfae [IsAffine X] [IsCountablyIndexedAffine Y]
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)] (f : X ⟶ Y) :
    List.TFAE [FormalAlgebraicSpace.LocallyOfFiniteType f, FiniteType f,
      exists_spfMap_isTaut_and_topologicallyOfFiniteType f] :=
  sorry

/-- For a morphism of affine formal algebraic spaces, locally of finite type
is equivalent to of finite type. -/
theorem locallyOfFiniteType_iff_finiteType [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) : FormalAlgebraicSpace.LocallyOfFiniteType f ↔ FiniteType f :=
  sorry

/-- An affine morphism of functors of points that is locally of finite type is
of finite type. -/
instance instFiniteType_of_locallyOfFiniteType [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) [FormalAlgebraicSpace.LocallyOfFiniteType f] : FiniteType f :=
  sorry

/-- For a morphism of affine formal algebraic spaces with countably indexed
target, locally of finite type is equivalent to corresponding to a taut
topologically finite-type arrow of `WAdm^count`. -/
theorem locallyOfFiniteType_iff_exists_spfMap_isTaut_and_topologicallyOfFiniteType
    [IsAffine X] [IsCountablyIndexedAffine Y]
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)] (f : X ⟶ Y) :
    FormalAlgebraicSpace.LocallyOfFiniteType f ↔ exists_spfMap_isTaut_and_topologicallyOfFiniteType f :=
  sorry

/-- For a morphism of affine formal algebraic spaces with countably indexed
target, of finite type is equivalent to corresponding to a taut topologically
finite-type arrow of `WAdm^count`. -/
theorem finiteType_iff_exists_spfMap_isTaut_and_topologicallyOfFiniteType
    [IsAffine X] [IsCountablyIndexedAffine Y]
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)] (f : X ⟶ Y) :
    FiniteType f ↔ exists_spfMap_isTaut_and_topologicallyOfFiniteType f :=
  sorry

end AlgebraicGeometry.AffineFormalAlgebraicSpace
