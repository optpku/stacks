/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import ReasLib.AlgebraicGeometry.FormalSpectrum.WeakIdeal
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening

/-!
# Formal spectra as colimits of affine thickenings

The formal spectrum is the fppf-sheaf colimit of the quotient spectra indexed
by all weak ideals of definition.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

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

/-- The formal spectrum is the fppf-sheaf colimit of the weak-ideal quotient spectra. -/
def spf (A : Type u) [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsWeaklyAdmissibleRing A] {S : Scheme.{u}}
    (structureHom : Spec (.of A) ⟶ S)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)] :
    Sheaf (Scheme.fppfTopology.over S) (Type u) :=
  colimit (thickenings A structureHom ⋙ yoneda ⋙
    presheafToSheaf (Scheme.fppfTopology.over S) (Type u))

/-- The formal spectrum equals the sheaf colimit of its quotient-stage diagram. -/
theorem spf_eq (A : Type u) [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsWeaklyAdmissibleRing A] {S : Scheme.{u}}
    (structureHom : Spec (.of A) ⟶ S)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)] :
    spf A structureHom =
      colimit (thickenings A structureHom ⋙ yoneda ⋙
        presheafToSheaf (Scheme.fppfTopology.over S) (Type u)) := sorry

/-- The colimit cocone leg from a sheafified quotient spectrum to the formal spectrum. -/
def spfι (A : Type u) [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsWeaklyAdmissibleRing A] {S : Scheme.{u}}
    (structureHom : Spec (.of A) ⟶ S)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]
    (I : WeakIdealOfDefinition A) :
    (presheafToSheaf (Scheme.fppfTopology.over S) (Type u)).obj
        (yoneda.obj (stage A structureHom I)) ⟶ spf A structureHom :=
  colimit.ι (thickenings A structureHom ⋙ yoneda ⋙
    presheafToSheaf (Scheme.fppfTopology.over S) (Type u)) I

/-- The quotient-spectrum map to the formal spectrum is the corresponding colimit leg. -/
theorem spfι_eq (A : Type u) [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsWeaklyAdmissibleRing A] {S : Scheme.{u}}
    (structureHom : Spec (.of A) ⟶ S)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)] (I : WeakIdealOfDefinition A) :
    spfι A structureHom I =
      colimit.ι (thickenings A structureHom ⋙ yoneda ⋙
        presheafToSheaf (Scheme.fppfTopology.over S) (Type u)) I := sorry

/-- The formal spectrum is isomorphic to the sheafification of its presheaf colimit. -/
def spf_iso_sheafify_presheafColimit (A : Type u) [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsWeaklyAdmissibleRing A] {S : Scheme.{u}}
    (structureHom : Spec (.of A) ⟶ S)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)] :
    spf A structureHom ≅
      (presheafToSheaf (Scheme.fppfTopology.over S) (Type u)).obj
        (colimit (thickenings A structureHom ⋙ yoneda)) :=
  (preservesColimitIso (presheafToSheaf (Scheme.fppfTopology.over S) (Type u))
    (thickenings A structureHom ⋙ yoneda)).symm

/-- The formal spectrum admits locally surjective maps from a sheafified
representable onto it and from another onto the first map's self-pullback. -/
theorem spf_existsPresentation (A : Type u) [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsWeaklyAdmissibleRing A] {S : Scheme.{u}}
    (structureHom : Spec (.of A) ⟶ S)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)] :
    ∃ (U R : Over S)
      (π : (presheafToSheaf (Scheme.fppfTopology.over S) (Type u)).obj (yoneda.obj U) ⟶
        spf A structureHom)
      (σ : (presheafToSheaf (Scheme.fppfTopology.over S) (Type u)).obj (yoneda.obj R) ⟶
        pullback π π),
      Sheaf.IsLocallySurjective π ∧ Sheaf.IsLocallySurjective σ := sorry

end AlgebraicGeometry.AffineFormalAlgebraicSpace
