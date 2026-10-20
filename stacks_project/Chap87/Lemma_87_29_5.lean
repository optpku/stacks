module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.ClosedImmersion.CountablyIndexed
import StacksCheckRecall

/-!
# Closed immersions into countably indexed affine formal algebraic spaces

A closed immersion of formal algebraic spaces into a countably indexed affine
formal algebraic space remains countably indexed affine. The corresponding
continuous map of weakly admissible topological `S`-algebras is the quotient
map `A →+* A ⧸ K` by a closed ideal.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.FormalAlgebraicSpace AlgebraicGeometry.AffineFormalAlgebraicSpace

noncomputable section

universe u

/- Lemma 87.29.5 (1): Let `S` be a scheme. Let `X` be a countably indexed
affine formal algebraic space over `S`. If `f : Y ⟶ X` is a closed immersion
of formal algebraic spaces over `S`, then `Y` is a countably indexed affine
formal algebraic space. -/
@[stacks 0AQI]
#check (AlgebraicGeometry.AffineFormalAlgebraicSpace.IsCountablyIndexedAffine.of_closedImmersion :
    ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsCountablyIndexedAffine X] [IsFormalAlgebraicSpace Y] (f : Y ⟶ X)
    [ClosedImmersion f], IsCountablyIndexedAffine Y)

/- Lemma 87.29.5 (2): Let `S` be a scheme. Let `X` be a countably indexed
affine formal algebraic space over `S`. If `f : Y ⟶ X` is a closed immersion
of formal algebraic spaces over `S`, then `f` corresponds to
`Ideal.Quotient.mk K : A →+* A ⧸ K` for a countably indexed weakly admissible
topological `S`-algebra `A` and a closed ideal `K`: there are isomorphisms
from the underlying functors of `spf A hA` and
`spf (A ⧸ K) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K)) ≫ hA)` to
`X` and `Y` identifying `f` with
`(sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).map
(spfMap (Ideal.Quotient.mk K) hφ rfl)`. -/
@[stacks 0AQI]
#check (AlgebraicGeometry.AffineFormalAlgebraicSpace.exists_spfMap_quotient_of_closedImmersion :
    ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsCountablyIndexedAffine X] [IsFormalAlgebraicSpace Y] (f : Y ⟶ X)
    [ClosedImmersion f]
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)],
    ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
      (_ : TopologicalRing.IsWeaklyAdmissibleRing A)
      (_ : TopologicalRing.IsCountablyIndexed A)
      (hA : Spec (.of A) ⟶ S) (K : Ideal A) (_ : IsClosed (K : Set A))
      (_ : TopologicalRing.IsWeaklyAdmissibleRing (A ⧸ K))
      (_ : TopologicalRing.IsCountablyIndexed (A ⧸ K))
      (hφ : Continuous (Ideal.Quotient.mk K))
      (eX : (sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).obj (spf A hA) ≅ X)
      (eY : (sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).obj
          (spf (A ⧸ K)
            (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K)) ≫ hA)) ≅ Y),
      eY.hom ≫ f =
        (sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).map
            (spfMap (Ideal.Quotient.mk K) hφ rfl) ≫ eX.hom)
