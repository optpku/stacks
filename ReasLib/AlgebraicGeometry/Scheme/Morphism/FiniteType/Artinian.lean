module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Affine.Artinian
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.RingTheory.LocalRing.Artinian.Residue

/-!
# Finite type morphisms from Artinian spectra

Finite type for a morphism from the spectrum of an Artinian local ring can be detected after
precomposition with the spectrum map induced by the residue homomorphism.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

/-- A morphism from the spectrum of an Artinian local ring is of finite type exactly when its
composition with the spectrum map of the residue homomorphism is of finite type. -/
theorem finiteType_iff_finiteType_comp_residueField
    {S : Scheme.{u}} {A : Type u} [CommRing A] [IsLocalRing A] [IsArtinianRing A]
    (f : Spec (CommRingCat.of A) ⟶ S) :
    FiniteType f ↔
      FiniteType (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ f) := sorry

end Scheme.Hom
end AlgebraicGeometry
