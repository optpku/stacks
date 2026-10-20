/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.ProjectiveBundle.ConormalAtlas
public import ReasLib.AlgebraicGeometry.Scheme.ProjectiveBundle.UniversalProperty

/-!
# Canonical conormal comparisons for projective bundles

These maps transport an explicit representative of an invertible quotient
class to the pullback of the tautological quotient and then apply the conormal
morphism constructed from symmetric homogeneous coordinates.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ProjectiveBundle.SymmetricPresentation.ConormalAtlas

variable {X P : Scheme.{u}} {ℰ : X.Modules} [ℰ.IsQuasicoherent]
variable {π : P ⟶ X} (S : SymmetricPresentation π ℰ) (A : ConormalAtlas S)

/-- The canonical isomorphism from the conormal object of a representative to that of the
concrete quotient attached to the same lift. -/
noncomputable def liftConormalRepresentativeIso {T : Scheme.{u}}
    (f : T ⟶ X) (σ : Lift π f)
    (q : CategoryTheory.InvertibleQuotient ((Scheme.Modules.pullback f).obj ℰ))
    (h : CategoryTheory.InvertibleQuotient.IsoClass.mk q =
      CategoryTheory.InvertibleQuotient.IsoClass.mk (S.liftSourceQuotient f σ)) :
    CategoryTheory.InvertibleQuotient.conormalObject q ≅
      CategoryTheory.InvertibleQuotient.conormalObject (S.liftSourceQuotient f σ) :=
  CategoryTheory.InvertibleQuotient.conormalObjectIso q (S.liftSourceQuotient f σ)
    (Iso.refl _) (CategoryTheory.InvertibleQuotient.targetIsoOfMkEq h)
    (CategoryTheory.InvertibleQuotient.targetIsoOfMkEq_spec h)

/-- The canonical conormal morphism attached to an explicit quotient representative
corresponding to a lift. -/
noncomputable def liftConormalMap {T : Scheme.{u}}
    (f : T ⟶ X) (σ : Lift π f)
    (q : CategoryTheory.InvertibleQuotient ((Scheme.Modules.pullback f).obj ℰ))
    (h : CategoryTheory.InvertibleQuotient.IsoClass.mk q =
      CategoryTheory.InvertibleQuotient.IsoClass.mk (S.liftSourceQuotient f σ)) :
    CategoryTheory.InvertibleQuotient.conormalObject q ⟶
      Scheme.Hom.conormalSheaf σ.baseChangeSection :=
  (liftConormalRepresentativeIso S f σ q h).hom ≫ A.map f σ

/-- The representative transport used in the lift conormal map is independent of every
compatible presentation of the same target isomorphism. -/
theorem liftConormalMap_targetIso_independent {T : Scheme.{u}}
    (f : T ⟶ X) (σ : Lift π f)
    (q : CategoryTheory.InvertibleQuotient ((Scheme.Modules.pullback f).obj ℰ))
    (h : CategoryTheory.InvertibleQuotient.IsoClass.mk q =
      CategoryTheory.InvertibleQuotient.IsoClass.mk (S.liftSourceQuotient f σ))
    (e : q.object ≅ (S.liftSourceQuotient f σ).object)
    (he : q.hom ≫ e.hom = (S.liftSourceQuotient f σ).hom) :
    (CategoryTheory.InvertibleQuotient.conormalObjectIso q
        (S.liftSourceQuotient f σ) (Iso.refl _) e he).hom ≫ A.map f σ =
      liftConormalMap S A f σ q h := sorry

/-- The canonical conormal morphism for a lift and a corresponding quotient representative is
an isomorphism. -/
theorem liftConormalMap_isIso {T : Scheme.{u}}
    (f : T ⟶ X) (σ : Lift π f)
    (q : CategoryTheory.InvertibleQuotient ((Scheme.Modules.pullback f).obj ℰ))
    (h : CategoryTheory.InvertibleQuotient.IsoClass.mk q =
      CategoryTheory.InvertibleQuotient.IsoClass.mk (S.liftSourceQuotient f σ)) :
    IsIso (liftConormalMap S A f σ q h) := sorry

/-- The identity-base-change transport of an invertible quotient representative. -/
noncomputable def sectionPullbackQuotient
    (q : CategoryTheory.InvertibleQuotient ℰ) :
    CategoryTheory.InvertibleQuotient ((Scheme.Modules.pullback (𝟙 X)).obj ℰ) :=
  CategoryTheory.InvertibleQuotient.precomposeIso
    ((Scheme.Modules.pullbackId X).app ℰ) q

/-- A quotient representing the class of a section continues to represent its concrete
tautological quotient after the canonical identity-pullback transport. -/
theorem sectionPullbackQuotient_class (σ : Lift π (𝟙 X))
    (q : CategoryTheory.InvertibleQuotient ℰ)
    (h : CategoryTheory.InvertibleQuotient.IsoClass.mk q =
      S.sectionToQuotientClass σ) :
    CategoryTheory.InvertibleQuotient.IsoClass.mk (sectionPullbackQuotient q) =
      CategoryTheory.InvertibleQuotient.IsoClass.mk
        (S.liftSourceQuotient (𝟙 X) σ) := sorry

/-- The conormal object of a section quotient is canonically identified with that of its
identity-base-change transport. -/
noncomputable def sectionPullbackConormalIso
    (q : CategoryTheory.InvertibleQuotient ℰ) :
    CategoryTheory.InvertibleQuotient.conormalObject q ≅
      CategoryTheory.InvertibleQuotient.conormalObject (sectionPullbackQuotient q) :=
  CategoryTheory.InvertibleQuotient.conormalObjectIso q (sectionPullbackQuotient q)
    ((Scheme.Modules.pullbackId X).app ℰ).symm (Iso.refl _)
    (by exact ((Scheme.Modules.pullbackId X).inv_hom_id_app_assoc ℰ q.hom).symm)

/-- The canonical morphism from a projective bundle to its base change along the identity of
the base. -/
noncomputable def sectionAmbientMap : P ⟶ pullback π (𝟙 X) :=
  pullback.lift (𝟙 P) π (by simp)

/-- A section and its identity-base-change section form the canonical ambient square. -/
def sectionConormalSquare (σ : Lift π (𝟙 X)) :
    CommSq (𝟙 X) σ.hom σ.baseChangeSection (sectionAmbientMap (π := π)) :=
  ⟨by
    apply pullback.hom_ext
    · simp only [Lift.baseChangeSection, sectionAmbientMap, pullback.lift_fst,
        Category.assoc, Category.comp_id, Category.id_comp]
    · simpa only [Lift.baseChangeSection, sectionAmbientMap, pullback.lift_snd,
        Category.assoc, Category.comp_id] using σ.fac.symm⟩

/-- The conormal sheaf of the identity-base-change section maps canonically to the conormal
sheaf of the original section. -/
noncomputable def sectionConormalTransport (σ : Lift π (𝟙 X)) :
    Scheme.Hom.conormalSheaf σ.baseChangeSection ⟶ Scheme.Hom.conormalSheaf σ.hom :=
  (Scheme.Modules.pullbackId X).inv.app
      (Scheme.Hom.conormalSheaf σ.baseChangeSection) ≫
    Scheme.Hom.Conormal.map (sectionConormalSquare (π := π) σ)

/-- The identity-base-change transport on section conormal sheaves is an isomorphism. -/
theorem sectionConormalTransport_isIso (σ : Lift π (𝟙 X)) :
    IsIso (sectionConormalTransport (π := π) σ) := sorry

/-- The canonical conormal morphism of a section, with codomain the conormal sheaf in the
original projective bundle. -/
noncomputable def sectionConormalMap (σ : Lift π (𝟙 X))
    (q : CategoryTheory.InvertibleQuotient ℰ)
    (h : CategoryTheory.InvertibleQuotient.IsoClass.mk q =
      S.sectionToQuotientClass σ) :
    CategoryTheory.InvertibleQuotient.conormalObject q ⟶
      Scheme.Hom.conormalSheaf σ.hom :=
  (sectionPullbackConormalIso q).hom ≫
    liftConormalMap S (ConormalAtlas.ofPresentation S) (𝟙 X) σ
      (sectionPullbackQuotient q) (sectionPullbackQuotient_class S σ q h) ≫
    sectionConormalTransport (π := π) σ

/-- The canonical conormal morphism of a section is an isomorphism. -/
theorem sectionConormalMap_isIso (σ : Lift π (𝟙 X))
    (q : CategoryTheory.InvertibleQuotient ℰ)
    (h : CategoryTheory.InvertibleQuotient.IsoClass.mk q =
      S.sectionToQuotientClass σ) :
    IsIso (sectionConormalMap S σ q h) := sorry

/-- The ambient comparison from the base change along `g ≫ f` to the base change along `f`. -/
noncomputable def precompAmbientMap {T R : Scheme.{u}} {f : T ⟶ X}
    (σ : Lift π f) (g : R ⟶ T) :
    pullback π (g ≫ f) ⟶ pullback π f :=
  pullback.lift (pullback.fst π (g ≫ f))
    (pullback.snd π (g ≫ f) ≫ g)
    (by simpa [Category.assoc] using pullback.condition (f := π) (g := g ≫ f))

/-- Precomposition of lifts gives the canonical square between their induced base-change
sections. -/
def precompConormalSquare {T R : Scheme.{u}} {f : T ⟶ X}
    (σ : Lift π f) (g : R ⟶ T) :
    CommSq g (σ.precomp g).baseChangeSection σ.baseChangeSection
      (precompAmbientMap (π := π) σ g) :=
  ⟨(Lift.baseChangeSection_precomp σ g).symm⟩

/-- The pulled-back representative, transported to the source determined by the composite
base morphism. -/
noncomputable def pullbackRepresentative {T R : Scheme.{u}}
    (f : T ⟶ X) (g : R ⟶ T)
    (q : CategoryTheory.InvertibleQuotient ((Scheme.Modules.pullback f).obj ℰ)) :
    CategoryTheory.InvertibleQuotient ((Scheme.Modules.pullback (g ≫ f)).obj ℰ) :=
  CategoryTheory.InvertibleQuotient.precomposeIso
    ((Scheme.Modules.pullbackComp g f).app ℰ).symm
    (CategoryTheory.InvertibleQuotient.pullback g q)

/-- Pulling back a representative corresponding to a lift gives a representative corresponding
to the precomposed lift. -/
theorem pullbackRepresentative_class {T R : Scheme.{u}}
    (f : T ⟶ X) (σ : Lift π f) (g : R ⟶ T)
    (q : CategoryTheory.InvertibleQuotient ((Scheme.Modules.pullback f).obj ℰ))
    (h : CategoryTheory.InvertibleQuotient.IsoClass.mk q =
      CategoryTheory.InvertibleQuotient.IsoClass.mk (S.liftSourceQuotient f σ)) :
    CategoryTheory.InvertibleQuotient.IsoClass.mk (pullbackRepresentative f g q) =
      CategoryTheory.InvertibleQuotient.IsoClass.mk
        (S.liftSourceQuotient (g ≫ f) (σ.precomp g)) := sorry

/-- The source comparison for the conormal object of a representative under arbitrary
precomposition. -/
noncomputable def liftConormalPullbackComparison {T R : Scheme.{u}}
    (f : T ⟶ X) (g : R ⟶ T)
    (q : CategoryTheory.InvertibleQuotient ((Scheme.Modules.pullback f).obj ℰ)) :
    (Scheme.Modules.pullback g).obj
        (CategoryTheory.InvertibleQuotient.conormalObject q) ⟶
      CategoryTheory.InvertibleQuotient.conormalObject (pullbackRepresentative f g q) :=
  CategoryTheory.InvertibleQuotient.pullbackConormalComparison g q ≫
    (CategoryTheory.InvertibleQuotient.conormalObjectIso
      (CategoryTheory.InvertibleQuotient.pullback g q)
      (pullbackRepresentative f g q)
      ((Scheme.Modules.pullbackComp g f).app ℰ) (Iso.refl _)
      (by
        exact ((Scheme.Modules.pullbackComp g f).hom_inv_id_app_assoc ℰ
          (CategoryTheory.InvertibleQuotient.pullback g q).hom).symm)).hom

/-- The explicit lift conormal maps commute with arbitrary precomposition through the quotient
and scheme-conormal pullback comparisons. -/
theorem liftConormalMap_precomp {T R : Scheme.{u}}
    (f : T ⟶ X) (σ : Lift π f) (g : R ⟶ T)
    (q : CategoryTheory.InvertibleQuotient ((Scheme.Modules.pullback f).obj ℰ))
    (h : CategoryTheory.InvertibleQuotient.IsoClass.mk q =
      CategoryTheory.InvertibleQuotient.IsoClass.mk (S.liftSourceQuotient f σ)) :
    (Scheme.Modules.pullback g).map
          (liftConormalMap S (ConormalAtlas.ofPresentation S) f σ q h) ≫
        Scheme.Hom.Conormal.map (precompConormalSquare (π := π) σ g) =
      liftConormalPullbackComparison (ℰ := ℰ) f g q ≫
        liftConormalMap S (ConormalAtlas.ofPresentation S) (g ≫ f) (σ.precomp g)
          (pullbackRepresentative f g q) (pullbackRepresentative_class S f σ g q h) := sorry

end AlgebraicGeometry.Scheme.ProjectiveBundle.SymmetricPresentation.ConormalAtlas
