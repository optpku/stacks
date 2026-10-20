module

public import ReasLib.AlgebraicGeometry.Scheme.Module.AffineRestriction
public import ReasLib.AlgebraicGeometry.Scheme.Module.CotangentComplex
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CotangentComplex.Homology
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Tilde.ChangeOfRings.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Basic
public import Mathlib.Algebra.Homology.Additive

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
private noncomputable def inverseImageSectionsMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    {U : X.Opens} {V : Y.Opens} (e : U ≤ f ⁻¹ᵁ V) :
    Γ(Y, V) →+*
      ((pullback CommRingCat.{u} f.toShHom.hom.base).obj Y.sheaf).obj.obj (op U) :=
  ((((pullbackPushforwardAdjunction CommRingCat.{u} f.toShHom.hom.base).unit.app
          Y.sheaf).hom.app (op V) ≫
      ((pullback CommRingCat.{u} f.toShHom.hom.base).obj Y.sheaf).obj.map
        (homOfLE e).op).hom)

/-- The inverse-image section-ring map and `f♯` on `U` recover the section-ring map
along `U ≤ f⁻¹(V)`. -/
private theorem inverseImageSectionsMap_comp {X Y : Scheme.{u}} (f : X ⟶ Y)
    {U : X.Opens} {V : Y.Opens} (e : U ≤ f ⁻¹ᵁ V) :
    ((RingedSpace.Hom.inverseImageStructureSheafHomComm f.toShHom).hom.app (op U)).hom.comp
        (inverseImageSectionsMap f e) =
      f.sectionsMapAlong V U e :=
  sorry

/-- Degreewise sections of the affine comparison, as a map of `Γ(X, U)`-modules. -/
@[no_expose] noncomputable def affineComparisonSections {X Y : Scheme.{u}} (f : X ⟶ Y)
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
        (by exact inverseImageSectionsMap_comp f e)).f i ≫
    (sectionsComplexMap
        (RingedSpace.Hom.inverseImageStructureSheafHomComm f.toShHom)
        (op U)).f i ≫
    (Scheme.Modules.affineOpenRestrictSectionsIso hU ((Hom.cotangentComplex f).X i)).hom

/-- The two canonical affine components commute with the cotangent differentials. -/
private theorem affineComparison_comm {X Y : Scheme.{u}} (f : X ⟶ Y)
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
  comm' := by exact affineComparison_comm f hU e

/-- Applying the tilde-Gamma adjunction to a component of `affineComparison` recovers
the corresponding sections map. -/
theorem affineComparison_homEquiv_spec {X Y : Scheme.{u}} (f : X ⟶ Y)
    {U : X.Opens} {V : Y.Opens} (hU : IsAffineOpen U) (e : U ≤ f ⁻¹ᵁ V) (i : ℤ) :
    (tilde.adjunction.homEquiv _ _) ((affineComparison f hU e).f i) =
      affineComparisonSections f hU e i :=
  sorry

/-- The section-ring maps of a scheme morphism form a commutative square under
restriction to nested opens. -/
private theorem sectionsMapAlong_restrict_square {X Y : Scheme.{u}} (f : X ⟶ Y)
    {U U' : X.Opens} {V V' : Y.Opens} (hUU' : U' ≤ U) (hVV' : V' ≤ V)
    (e : U ≤ f ⁻¹ᵁ V) (e' : U' ≤ f ⁻¹ᵁ V') :
    (f.sectionsMapAlong V' U' e').comp (Y.presheaf.map (homOfLE hVV').op).hom =
      (X.presheaf.map (homOfLE hUU').op).hom.comp (f.sectionsMapAlong V U e) :=
  sorry

/-- The canonical comparison on an affine source open over an affine target open
becomes an isomorphism in the derived category. -/
instance affineComparison_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    {U : X.Opens} {V : Y.Opens} (hU : IsAffineOpen U) [hV : Fact (IsAffineOpen V)]
    (e : U ≤ f ⁻¹ᵁ V) :
    IsIso (DerivedCategory.Q.map (affineComparison f hU e)) :=
  sorry

/-- The canonical affine comparison commutes with restriction to smaller affine
opens in the source and target. -/
theorem affineComparison_restrict {X Y : Scheme.{u}} (f : X ⟶ Y)
    {U U' : X.Opens} {V V' : Y.Opens}
    (hU : IsAffineOpen U) (hU' : IsAffineOpen U')
    (hV : IsAffineOpen V) (hV' : IsAffineOpen V')
    (hUU' : U' ≤ U) (hVV' : V' ≤ V)
    (e : U ≤ f ⁻¹ᵁ V) (e' : U' ≤ f ⁻¹ᵁ V') :
    (Pullback.mapHomologicalComplexIso
          (X.presheaf.map (homOfLE hUU').op) (up ℤ)).hom.app
          (RingHom.cotangentComplex (f.sectionsMapAlong V U e)) ≫
        ((tilde.functor (CommRingCat.of Γ(X, U'))).mapHomologicalComplex (up ℤ)).map
          (Algebra.CotangentComplex.map (f.sectionsMapAlong V U e)
            (f.sectionsMapAlong V' U' e')
            (Y.presheaf.map (homOfLE hVV').op).hom
            (X.presheaf.map (homOfLE hUU').op).hom
            (by exact sectionsMapAlong_restrict_square f hUU' hVV' e e')) ≫
        affineComparison f hU' e' =
      ((Modules.pullback
            (Spec.map (X.presheaf.map (homOfLE hUU').op))).mapHomologicalComplex
          (up ℤ)).map
          (affineComparison f hU e) ≫
        (Functor.mapHomologicalComplexCompIso
          (Scheme.Modules.nestedAffinePullbackIso hU hU' hUU') (up ℤ)).hom.app
          (Hom.cotangentComplex f) :=
  sorry

end AlgebraicGeometry.Scheme.Hom.CotangentComplex
