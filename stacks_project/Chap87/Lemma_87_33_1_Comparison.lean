module

public import ReasLib.AlgebraicGeometry.FormalSpectrum.Comparison

/-!
# Comparison from Spf to Spec

The canonical morphism `Spf(A) ⟶ Spec(A)` of sheaves over `S` is the colimit
of the sheafified Yoneda images of the affine stages `Spec(A ⧸ I) ⟶ Spec(A)`.
Precomposition yields the natural map on morphisms into an `S`-scheme.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

open AlgebraicGeometry.AffineFormalAlgebraicSpace

#check (AlgebraicGeometry.AffineFormalAlgebraicSpace.specHomToSpfHom :
  ∀ {A : Type u} [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsWeaklyAdmissibleRing A] {S : Scheme.{u}}
    (structureHom : Spec (.of A) ⟶ S) (X : Over S)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)],
    (Over.mk structureHom ⟶ X) →
      (spf A structureHom ⟶
        (presheafToSheaf (Scheme.fppfTopology.over S) (Type u)).obj
          (yoneda.obj X)))
