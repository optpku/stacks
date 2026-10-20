module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import ReasLib.AlgebraicGeometry.FormalSpectrum.WeakIdeal
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening

/-!
# Quotient-spectrum diagrams

Weak ideals of definition index quotient spectra with thickening transitions.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

/-- The quotient spectrum `Spec(A ⧸ I)` over the base scheme. -/
def stage (A : Type u) [CommRing A] [TopologicalSpace A] {S : Scheme.{u}}
    (structureHom : Spec (.of A) ⟶ S) (I : WeakIdealOfDefinition A) : Over S :=
  Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I.ideal)) ≫ structureHom)

/-- The underlying scheme of a quotient stage is its quotient spectrum. -/
theorem stage_left (A : Type u) [CommRing A] [TopologicalSpace A] {S : Scheme.{u}}
    (structureHom : Spec (.of A) ⟶ S) (I : WeakIdealOfDefinition A) :
    (stage A structureHom I).left = Spec (.of (A ⧸ I.ideal)) := sorry

/-- The quotient-spectrum transition commutes with the morphisms to the base. -/
theorem transition_comm (A : Type u) [CommRing A] [TopologicalSpace A] {S : Scheme.{u}}
    (structureHom : Spec (.of A) ⟶ S) {I J : WeakIdealOfDefinition A} (f : I ⟶ J) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (leOfHom f : J.ideal ≤ I.ideal))) ≫
      (stage A structureHom J).hom = (stage A structureHom I).hom := sorry

/-- Reverse inclusion of weak ideals induces the quotient-spectrum morphism over the base. -/
def transition (A : Type u) [CommRing A] [TopologicalSpace A] {S : Scheme.{u}}
    (structureHom : Spec (.of A) ⟶ S) {I J : WeakIdealOfDefinition A} (f : I ⟶ J) :
    stage A structureHom I ⟶ stage A structureHom J :=
  Over.homMk
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (leOfHom f : J.ideal ≤ I.ideal))))
    (transition_comm A structureHom f)

/-- The transition associated to an identity is the identity of its quotient stage. -/
theorem transition_id (A : Type u) [CommRing A] [TopologicalSpace A] {S : Scheme.{u}}
    (structureHom : Spec (.of A) ⟶ S) (I : WeakIdealOfDefinition A) :
    transition A structureHom (𝟙 I) = 𝟙 (stage A structureHom I) := sorry

/-- Quotient-spectrum transitions preserve composition in the reverse-inclusion index. -/
theorem transition_comp (A : Type u) [CommRing A] [TopologicalSpace A] {S : Scheme.{u}}
    (structureHom : Spec (.of A) ⟶ S) {I J K : WeakIdealOfDefinition A}
    (f : I ⟶ J) (g : J ⟶ K) :
    transition A structureHom (f ≫ g) =
      transition A structureHom f ≫ transition A structureHom g := sorry

/-- The diagram of quotient spectra and their transition morphisms over the base. -/
def thickenings (A : Type u) [CommRing A] [TopologicalSpace A] {S : Scheme.{u}}
    (structureHom : Spec (.of A) ⟶ S) : WeakIdealOfDefinition A ⥤ Over S where
  obj I := stage A structureHom I
  map f := transition A structureHom f
  map_id I := transition_id A structureHom I
  map_comp f g := transition_comp A structureHom f g

/-- Objects of the quotient-spectrum diagram are the quotient stages. -/
theorem thickenings_obj (A : Type u) [CommRing A] [TopologicalSpace A] {S : Scheme.{u}}
    (structureHom : Spec (.of A) ⟶ S) (I : WeakIdealOfDefinition A) :
    (thickenings A structureHom).obj I = stage A structureHom I := sorry

/-- Every quotient stage is an affine scheme. -/
instance thickenings_obj_isAffine (A : Type u) [CommRing A] [TopologicalSpace A]
    {S : Scheme.{u}} (structureHom : Spec (.of A) ⟶ S) (I : WeakIdealOfDefinition A) :
    IsAffine (stage A structureHom I).left := sorry

/-- Transition morphisms between weak-ideal quotient spectra are thickenings. -/
instance thickenings_map_isThickening (A : Type u) [CommRing A] [TopologicalSpace A]
    {S : Scheme.{u}} (structureHom : Spec (.of A) ⟶ S) {I J : WeakIdealOfDefinition A}
    (f : I ⟶ J) : IsThickening ((thickenings A structureHom).map f).left := sorry

end AlgebraicGeometry.AffineFormalAlgebraicSpace
