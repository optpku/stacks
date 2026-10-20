module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.McQuillan
public import ReasLib.AlgebraicGeometry.FormalSpectrum.ClosedImmersion
public import ReasLib.AlgebraicGeometry.FormalSpectrum.Representable

/-!
# Closed immersions into McQuillan affine formal algebraic spaces

A closed immersion into a McQuillan affine formal algebraic space has McQuillan
affine source and is induced by a continuous homomorphism with tautness,
closed kernel, and dense image.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.FormalAlgebraicSpace AlgebraicGeometry.AffineFormalAlgebraicSpace

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- A closed immersion into a McQuillan affine formal algebraic space over a
scheme has McQuillan affine source and admits compatible formal-spectrum
presentations induced by a continuous homomorphism of weakly admissible
topological rings that is taut, has closed kernel, and has dense image. -/
theorem exists_spfMap_iso_of_closedImmersion
    {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsMcQuillanAffine X] [IsFormalAlgebraicSpace Y] (f : Y ⟶ X)
    [ClosedImmersion f]
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)] :
    IsMcQuillanAffine Y ∧
    ∃ (A B : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
      (_ : TopologicalRing.IsWeaklyAdmissibleRing A) (_ : CommRing B)
      (_ : TopologicalSpace B) (_ : TopologicalRing.IsWeaklyAdmissibleRing B)
      (hA : Spec (.of A) ⟶ S) (hB : Spec (.of B) ⟶ S) (φ : A →+* B)
      (hφ : Continuous φ) (h_over : Spec.map (CommRingCat.ofHom φ) ≫ hA = hB)
      (eX : (sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).obj (spf A hA) ≅ X)
      (eY : (sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).obj (spf B hB) ≅ Y),
      (eY.hom ≫ f =
        (sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).map
            (spfMap φ hφ h_over) ≫ eX.hom) ∧
        φ.IsTaut ∧ IsClosed (RingHom.ker φ : Set A) ∧ DenseRange φ :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace
