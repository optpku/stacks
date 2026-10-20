module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.McQuillan.ClosedImmersion
import StacksCheckRecall

/-!
# Closed immersions into McQuillan affine formal algebraic spaces

A closed immersion into a McQuillan affine formal algebraic space has McQuillan
affine source and corresponds to a continuous homomorphism of weakly admissible
topological algebras that is taut, has closed kernel, and has dense image.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.FormalAlgebraicSpace AlgebraicGeometry.AffineFormalAlgebraicSpace

universe u

/- Lemma 87.27.5 -/
@[stacks 0ANQ] #check
  (AlgebraicGeometry.FormalAlgebraicSpace.exists_spfMap_iso_of_closedImmersion :
    ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsMcQuillanAffine X] [IsFormalAlgebraicSpace Y] (f : Y ⟶ X)
    [ClosedImmersion f]
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)],
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
        φ.IsTaut ∧ IsClosed (RingHom.ker φ : Set A) ∧ DenseRange φ)
