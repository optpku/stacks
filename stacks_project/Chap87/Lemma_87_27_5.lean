module

public import stacks_project.Chap87.Lemma_87_27_5_McQuillan
public import stacks_project.Chap87.Lemma_87_27_3_ClosedImmersion
public import stacks_project.Chap87.Lemma_87_9_10_Map
public import stacks_project.Chap87.Definition_87_5_1_Taut

/-!
# Closed immersions into McQuillan affine formal algebraic spaces

A closed immersion of formal algebraic spaces into a McQuillan affine formal
algebraic space remains McQuillan affine. The corresponding continuous map of
weakly admissible topological `S`-algebras is taut, has closed kernel, and has
dense image.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.FormalAlgebraicSpace AlgebraicGeometry.AffineFormalAlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

namespace IsMcQuillanAffine

/-- Lemma 87.27.5 (1): Let `S` be a scheme. Let `X` be a McQuillan affine
formal algebraic space over `S`. If `f : Y ⟶ X` is a closed immersion of
formal algebraic spaces over `S`, then `Y` is McQuillan affine. -/
@[stacks 0ANQ]
theorem of_closedImmersion {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsMcQuillanAffine X] [IsFormalAlgebraicSpace Y] (f : Y ⟶ X)
    [ClosedImmersion f] : IsMcQuillanAffine Y :=
  sorry

end IsMcQuillanAffine

/-- Lemma 87.27.5 (2): Let `S` be a scheme. Let `X` be a McQuillan affine
formal algebraic space over `S`. If `f : Y ⟶ X` is a closed immersion of
formal algebraic spaces over `S`, then `f` corresponds to a continuous
homomorphism `φ : A →+* B` of weakly admissible topological `S`-algebras:
there are isomorphisms from the underlying functors of `spf A hA` and
`spf B hB` to `X` and `Y` identifying `f` with
`(sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).map (spfMap φ hφ h_over)`. -/
@[stacks 0ANQ]
theorem exists_spfMap_iso_of_closedImmersion
    {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsMcQuillanAffine X] [IsFormalAlgebraicSpace Y] (f : Y ⟶ X)
    [ClosedImmersion f]
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)] :
    ∃ (A B : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
      (_ : TopologicalRing.IsWeaklyAdmissibleRing A) (_ : CommRing B)
      (_ : TopologicalSpace B) (_ : TopologicalRing.IsWeaklyAdmissibleRing B)
      (hA : Spec (.of A) ⟶ S) (hB : Spec (.of B) ⟶ S) (φ : A →+* B)
      (hφ : Continuous φ) (h_over : Spec.map (CommRingCat.ofHom φ) ≫ hA = hB)
      (eX : (sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).obj (spf A hA) ≅ X)
      (eY : (sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).obj (spf B hB) ≅ Y),
      eY.hom ≫ f =
        (sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).map
            (spfMap φ hφ h_over) ≫ eX.hom :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

/-- Lemma 87.27.5 (3): Let `S` be a scheme. Let `X` be a McQuillan affine
formal algebraic space over `S`. If `f : Y ⟶ X` is a closed immersion of
formal algebraic spaces over `S` corresponding to a continuous homomorphism
`φ : A →+* B` of weakly admissible topological `S`-algebras via
`eY.hom ≫ f = (sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).map
(spfMap φ hφ h_over) ≫ eX.hom`, then `φ` is taut. -/
@[stacks 0ANQ]
theorem isTaut_of_closedImmersion_spfMap
    {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsMcQuillanAffine X] [IsFormalAlgebraicSpace Y] (f : Y ⟶ X)
    [ClosedImmersion f] {A B : Type u}
    [CommRing A] [TopologicalSpace A] [TopologicalRing.IsWeaklyAdmissibleRing A]
    [CommRing B] [TopologicalSpace B] [TopologicalRing.IsWeaklyAdmissibleRing B]
    (hA : Spec (.of A) ⟶ S) (hB : Spec (.of B) ⟶ S) (φ : A →+* B)
    (hφ : Continuous φ) (h_over : Spec.map (CommRingCat.ofHom φ) ≫ hA = hB)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]
    (eX : (sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).obj (spf A hA) ≅ X)
    (eY : (sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).obj (spf B hB) ≅ Y)
    (h_corresponds : eY.hom ≫ f =
      (sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).map
          (spfMap φ hφ h_over) ≫ eX.hom) :
    φ.IsTaut :=
  sorry

/-- Lemma 87.27.5 (4): Let `S` be a scheme. Let `X` be a McQuillan affine
formal algebraic space over `S`. If `f : Y ⟶ X` is a closed immersion of
formal algebraic spaces over `S` corresponding to a continuous homomorphism
`φ : A →+* B` of weakly admissible topological `S`-algebras via
`eY.hom ≫ f = (sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).map
(spfMap φ hφ h_over) ≫ eX.hom`, then the kernel of `φ` is closed. -/
@[stacks 0ANQ]
theorem isClosed_ker_of_closedImmersion_spfMap
    {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsMcQuillanAffine X] [IsFormalAlgebraicSpace Y] (f : Y ⟶ X)
    [ClosedImmersion f] {A B : Type u}
    [CommRing A] [TopologicalSpace A] [TopologicalRing.IsWeaklyAdmissibleRing A]
    [CommRing B] [TopologicalSpace B] [TopologicalRing.IsWeaklyAdmissibleRing B]
    (hA : Spec (.of A) ⟶ S) (hB : Spec (.of B) ⟶ S) (φ : A →+* B)
    (hφ : Continuous φ) (h_over : Spec.map (CommRingCat.ofHom φ) ≫ hA = hB)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]
    (eX : (sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).obj (spf A hA) ≅ X)
    (eY : (sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).obj (spf B hB) ≅ Y)
    (h_corresponds : eY.hom ≫ f =
      (sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).map
          (spfMap φ hφ h_over) ≫ eX.hom) :
    IsClosed (RingHom.ker φ : Set A) :=
  sorry

/-- Lemma 87.27.5 (5): Let `S` be a scheme. Let `X` be a McQuillan affine
formal algebraic space over `S`. If `f : Y ⟶ X` is a closed immersion of
formal algebraic spaces over `S` corresponding to a continuous homomorphism
`φ : A →+* B` of weakly admissible topological `S`-algebras via
`eY.hom ≫ f = (sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).map
(spfMap φ hφ h_over) ≫ eX.hom`, then `φ` has dense image. -/
@[stacks 0ANQ]
theorem denseRange_of_closedImmersion_spfMap
    {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsMcQuillanAffine X] [IsFormalAlgebraicSpace Y] (f : Y ⟶ X)
    [ClosedImmersion f] {A B : Type u}
    [CommRing A] [TopologicalSpace A] [TopologicalRing.IsWeaklyAdmissibleRing A]
    [CommRing B] [TopologicalSpace B] [TopologicalRing.IsWeaklyAdmissibleRing B]
    (hA : Spec (.of A) ⟶ S) (hB : Spec (.of B) ⟶ S) (φ : A →+* B)
    (hφ : Continuous φ) (h_over : Spec.map (CommRingCat.ofHom φ) ≫ hA = hB)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]
    (eX : (sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).obj (spf A hA) ≅ X)
    (eY : (sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).obj (spf B hB) ≅ Y)
    (h_corresponds : eY.hom ≫ f =
      (sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).map
          (spfMap φ hφ h_over) ≫ eX.hom) :
    DenseRange φ :=
  sorry

end AlgebraicGeometry.AffineFormalAlgebraicSpace
