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
public import ReasLib.AlgebraicGeometry.FormalSpectrum.QuotientDiagram
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
