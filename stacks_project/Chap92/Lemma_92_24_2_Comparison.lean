/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap92.Definition_92_24_1_Morphism
public import stacks_project.Chap92.Lemma_92_18_4_Homology
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Tilde.ChangeOfRings.Pullback
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Affine comparison for the cotangent complex of a scheme morphism

Canonical map of complexes `tilde(L_{Γ(X,U)/Γ(Y,V)}) ⟶ L_{X/Y}` restricted along
`fromSpec` of an affine open `U ⊆ f⁻¹(V)`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ComplexShape
open HomologicalComplex Opposite TopCat.Sheaf
open SheafOfModules.RingedSite.CotangentComplex
open SheafOfModules.RingedSite.CotangentComplex.Homology
open AlgebraicGeometry.tilde.ChangeOfRings
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.CotangentComplex

/-- The canonical ring map `Γ(Y, V) →+* (f⁻¹ O_Y)(U)` induced by the unit of
pullback-pushforward adjunction and restriction along `U ≤ f⁻¹(V)`. -/
noncomputable def inverseImageSectionsMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    {U : X.Opens} {V : Y.Opens} (e : U ≤ f ⁻¹ᵁ V) :
    Γ(Y, V) →+*
      ((pullback CommRingCat.{u} f.toShHom.hom.base).obj Y.sheaf).obj.obj (op U) :=
  ((((pullbackPushforwardAdjunction CommRingCat.{u} f.toShHom.hom.base).unit.app
          Y.sheaf).hom.app (op V) ≫
      ((pullback CommRingCat.{u} f.toShHom.hom.base).obj Y.sheaf).obj.map
        (homOfLE e).op).hom)

/-- The inverse-image section-ring map and `f♯` on `U` recover the section-ring map
along `U ≤ f⁻¹(V)`. -/
theorem inverseImageSectionsMap_comp {X Y : Scheme.{u}} (f : X ⟶ Y)
    {U : X.Opens} {V : Y.Opens} (e : U ≤ f ⁻¹ᵁ V) :
    ((RingedSpace.Hom.inverseImageStructureSheafHomComm f.toShHom).hom.app (op U)).hom.comp
        (inverseImageSectionsMap f e) =
      f.sectionsMapAlong V U e :=
  sorry

/-- Scalar compatibility for the affine-open identification of module sections with
global sections of the restriction along `fromSpec`. -/
theorem affineOpenRestrictSectionsIso_smul {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (M : X.Modules) (r : Γ(X, U)) :
    (M.presheaf.mapIso
            (eqToIso
              (hU.fromSpec.image_top_eq_opensRange.trans
                hU.opensRange_fromSpec)).op).hom ≫
        (M.restrictAppIso hU.fromSpec ⊤).inv ≫
          ((moduleSpecΓFunctor (R := Γ(X, U))).obj
            ((Scheme.Modules.restrictFunctor hU.fromSpec).obj M)).smul r =
      ((SheafOfModules.evaluation.{u} X.ringCatSheaf (op U)).obj M).smul r ≫
        (M.presheaf.mapIso
            (eqToIso
              (hU.fromSpec.image_top_eq_opensRange.trans
                hU.opensRange_fromSpec)).op).hom ≫
          (M.restrictAppIso hU.fromSpec ⊤).inv :=
  sorry

/-- Canonical identification of sections of `M` on an affine open `U` with global
sections of the restriction of `M` along `hU.fromSpec`. -/
noncomputable def affineOpenRestrictSectionsIso {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (M : X.Modules) :
    (SheafOfModules.evaluation.{u} X.ringCatSheaf (op U)).obj M ≅
      (moduleSpecΓFunctor (R := Γ(X, U))).obj
        ((Scheme.Modules.restrictFunctor hU.fromSpec).obj M) :=
  ModuleCat.isoMk
    (M.presheaf.mapIso
        (eqToIso
          (hU.fromSpec.image_top_eq_opensRange.trans
            hU.opensRange_fromSpec)).op ≪≫
      (M.restrictAppIso hU.fromSpec ⊤).symm)
    (affineOpenRestrictSectionsIso_smul hU M)

/-- Degreewise sections of the affine comparison, as a map of `Γ(X, U)`-modules. -/
noncomputable def affineComparisonSections {X Y : Scheme.{u}} (f : X ⟶ Y)
    {U : X.Opens} {V : Y.Opens} (hU : IsAffineOpen U) (e : U ≤ f ⁻¹ᵁ V) (i : ℤ) :
    (RingHom.cotangentComplex (f.sectionsMapAlong V U e)).X i ⟶
      (moduleSpecΓFunctor (R := Γ(X, U))).obj
        ((((Scheme.Modules.restrictFunctor hU.fromSpec).mapHomologicalComplex
            (up ℤ)).obj (Hom.cotangentComplex f)).X i) :=
  (ModuleCat.extendScalarsId Γ(X, U)).inv.app
      ((RingHom.cotangentComplex (f.sectionsMapAlong V U e)).X i) ≫
    (Algebra.CotangentComplex.map (f.sectionsMapAlong V U e)
        ((RingedSpace.Hom.inverseImageStructureSheafHomComm f.toShHom).hom.app
          (op U)).hom
        (inverseImageSectionsMap f e) (RingHom.id Γ(X, U))
        (inverseImageSectionsMap_comp f e)).f i ≫
    (sectionsComplexMap
        (RingedSpace.Hom.inverseImageStructureSheafHomComm f.toShHom)
        (op U)).f i ≫
    (affineOpenRestrictSectionsIso hU ((Hom.cotangentComplex f).X i)).hom

/-- The two canonical affine components commute with the cotangent differentials. -/
theorem affineComparison_comm {X Y : Scheme.{u}} (f : X ⟶ Y)
    {U : X.Opens} {V : Y.Opens} (hU : IsAffineOpen U) (e : U ≤ f ⁻¹ᵁ V)
    (i j : ℤ) (_ : (up ℤ).Rel i j) :
    (tilde.adjunction.homEquiv _ _).symm (affineComparisonSections f hU e i) ≫
        ((((Scheme.Modules.restrictFunctor hU.fromSpec).mapHomologicalComplex
            (up ℤ)).obj (Hom.cotangentComplex f)).d i j) =
      ((((tilde.functor (CommRingCat.of Γ(X, U))).mapHomologicalComplex (up ℤ)).obj
            (RingHom.cotangentComplex (f.sectionsMapAlong V U e))).d i j) ≫
        (tilde.adjunction.homEquiv _ _).symm (affineComparisonSections f hU e j) :=
  sorry

/-- The affine comparison from the tilde of the algebraic cotangent complex of the
section-ring map along `U ⊆ f⁻¹(V)` to the restriction of `L_f` along `fromSpec`. -/
noncomputable def affineComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    {U : X.Opens} {V : Y.Opens} (hU : IsAffineOpen U) (e : U ≤ f ⁻¹ᵁ V) :
    ((tilde.functor (CommRingCat.of Γ(X, U))).mapHomologicalComplex (up ℤ)).obj
        (RingHom.cotangentComplex (f.sectionsMapAlong V U e)) ⟶
      ((Scheme.Modules.restrictFunctor hU.fromSpec).mapHomologicalComplex (up ℤ)).obj
        (Hom.cotangentComplex f) where
  f i := (tilde.adjunction.homEquiv _ _).symm (affineComparisonSections f hU e i)
  comm' := affineComparison_comm f hU e

/-- Applying the tilde-Gamma adjunction to a component of `affineComparison` recovers
the corresponding sections map. -/
theorem affineComparison_homEquiv_spec {X Y : Scheme.{u}} (f : X ⟶ Y)
    {U : X.Opens} {V : Y.Opens} (hU : IsAffineOpen U) (e : U ≤ f ⁻¹ᵁ V) (i : ℤ) :
    (tilde.adjunction.homEquiv _ _) ((affineComparison f hU e).f i) =
      affineComparisonSections f hU e i :=
  sorry

/-- The section-ring maps of a scheme morphism form a commutative square under
restriction to nested opens. -/
theorem sectionsMapAlong_restrict_square {X Y : Scheme.{u}} (f : X ⟶ Y)
    {U U' : X.Opens} {V V' : Y.Opens} (hUU' : U' ≤ U) (hVV' : V' ≤ V)
    (e : U ≤ f ⁻¹ᵁ V) (e' : U' ≤ f ⁻¹ᵁ V') :
    (f.sectionsMapAlong V' U' e').comp (Y.presheaf.map (homOfLE hVV').op).hom =
      (X.presheaf.map (homOfLE hUU').op).hom.comp (f.sectionsMapAlong V U e) :=
  sorry

/-- Identification of pullback along `Spec` of restriction of functions on nested
affine opens with restriction along `fromSpec` of the smaller open. -/
noncomputable def nestedAffinePullbackIso {X : Scheme.{u}} {U U' : X.Opens}
    (hU : IsAffineOpen U) (hU' : IsAffineOpen U') (hLE : U' ≤ U) :
    Scheme.Modules.restrictFunctor hU.fromSpec ⋙
        Scheme.Modules.pullback (Spec.map (X.presheaf.map (homOfLE hLE).op)) ≅
      Scheme.Modules.restrictFunctor hU'.fromSpec :=
  Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback hU.fromSpec)
      (Scheme.Modules.pullback (Spec.map (X.presheaf.map (homOfLE hLE).op))) ≪≫
    Scheme.Modules.pullbackComp (Spec.map (X.presheaf.map (homOfLE hLE).op))
      hU.fromSpec ≪≫
    Scheme.Modules.pullbackCongr
      (IsAffineOpen.map_fromSpec hU hU' (homOfLE hLE).op) ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback hU'.fromSpec).symm

/-- The two canonical change-of-rings components commute with differentials. -/
theorem affineComparisonPullbackIso_comm {X : Scheme.{u}} {U U' : X.Opens}
    (hLE : U' ≤ U) (K : CochainComplex (ModuleCat.{u} Γ(X, U)) ℤ)
    (i j : ℤ) (_ : (up ℤ).Rel i j) :
    (Pullback.iso (X.presheaf.map (homOfLE hLE).op)).hom.app (K.X i) ≫
        ((((tilde.functor (CommRingCat.of Γ(X, U'))).mapHomologicalComplex (up ℤ)).obj
            (((ModuleCat.extendScalars
                (X.presheaf.map (homOfLE hLE).op).hom).mapHomologicalComplex
              (up ℤ)).obj K)).d i j) =
      ((((Scheme.Modules.pullback
              (Spec.map (X.presheaf.map (homOfLE hLE).op))).mapHomologicalComplex
            (up ℤ)).obj
          (((tilde.functor (CommRingCat.of Γ(X, U))).mapHomologicalComplex (up ℤ)).obj
            K)).d i j) ≫
        (Pullback.iso (X.presheaf.map (homOfLE hLE).op)).hom.app (K.X j) :=
  sorry

/-- Change of rings for the tilde of a cochain complex of `Γ(X, U)`-modules along
restriction of functions to a smaller affine open. -/
noncomputable def affineComparisonPullbackIso {X : Scheme.{u}} {U U' : X.Opens}
    (hLE : U' ≤ U) (K : CochainComplex (ModuleCat.{u} Γ(X, U)) ℤ) :
    ((Scheme.Modules.pullback
          (Spec.map (X.presheaf.map (homOfLE hLE).op))).mapHomologicalComplex
        (up ℤ)).obj
        (((tilde.functor (CommRingCat.of Γ(X, U))).mapHomologicalComplex (up ℤ)).obj K) ⟶
      ((tilde.functor (CommRingCat.of Γ(X, U'))).mapHomologicalComplex (up ℤ)).obj
        (((ModuleCat.extendScalars
            (X.presheaf.map (homOfLE hLE).op).hom).mapHomologicalComplex (up ℤ)).obj K) where
  f i := (Pullback.iso (X.presheaf.map (homOfLE hLE).op)).hom.app (K.X i)
  comm' := affineComparisonPullbackIso_comm hLE K

/-- The nested affine identification commutes with differentials. -/
theorem nestedAffinePullbackIso_map_comm {X : Scheme.{u}} {U U' : X.Opens}
    (hU : IsAffineOpen U) (hU' : IsAffineOpen U') (hLE : U' ≤ U)
    (K : CochainComplex X.Modules ℤ) (i j : ℤ) (_ : (up ℤ).Rel i j) :
    (nestedAffinePullbackIso hU hU' hLE).hom.app (K.X i) ≫
        ((((Scheme.Modules.restrictFunctor hU'.fromSpec).mapHomologicalComplex
            (up ℤ)).obj K).d i j) =
      ((((Scheme.Modules.pullback
              (Spec.map (X.presheaf.map (homOfLE hLE).op))).mapHomologicalComplex
            (up ℤ)).obj
          (((Scheme.Modules.restrictFunctor hU.fromSpec).mapHomologicalComplex
            (up ℤ)).obj K)).d i j) ≫
        (nestedAffinePullbackIso hU hU' hLE).hom.app (K.X j) :=
  sorry

/-- The nested affine identification, prolonged to cochain complexes. -/
noncomputable def nestedAffinePullbackIso_map {X : Scheme.{u}} {U U' : X.Opens}
    (hU : IsAffineOpen U) (hU' : IsAffineOpen U') (hLE : U' ≤ U)
    (K : CochainComplex X.Modules ℤ) :
    ((Scheme.Modules.pullback
          (Spec.map (X.presheaf.map (homOfLE hLE).op))).mapHomologicalComplex
        (up ℤ)).obj
        (((Scheme.Modules.restrictFunctor hU.fromSpec).mapHomologicalComplex (up ℤ)).obj K) ⟶
      ((Scheme.Modules.restrictFunctor hU'.fromSpec).mapHomologicalComplex (up ℤ)).obj K where
  f i := (nestedAffinePullbackIso hU hU' hLE).hom.app (K.X i)
  comm' := nestedAffinePullbackIso_map_comm hU hU' hLE K

end AlgebraicGeometry.Scheme.Hom.CotangentComplex
