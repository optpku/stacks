/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.NaiveCotangent
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.Canonical
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.Reindex
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.AlgebraicGeometry.Modules.Tilde

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Sheaf ComplexShape HomologicalComplex
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.NaiveCotangent

/-- The evaluation of the canonical polynomial self-presentation of the section-ring map. -/
@[no_expose]
noncomputable def affineEvaluation
    {X Y : Scheme.{u}} (f : X ⟶ Y) {U : X.Opens} {V : Y.Opens}
    (e : U ≤ f ⁻¹ᵁ V) : MvPolynomial Γ(X, U) Γ(Y, V) →+* Γ(X, U) :=
  MvPolynomial.eval₂Hom (f.sectionsMapAlong V U e) id

/-- The canonical polynomial map from the self-presentation of the affine section-ring map to
the sections on `U` of the canonical sheaf polynomial presentation of `f`. -/
@[no_expose]
noncomputable def affinePolynomialMap
    {X Y : Scheme.{u}} (f : X ⟶ Y) {U : X.Opens} {V : Y.Opens}
    (e : U ≤ f ⁻¹ᵁ V) :
    MvPolynomial Γ(X, U) Γ(Y, V) →+*
      (CategoryTheory.Sheaf.FreeAlgebra.Presentation.underlying
        ((TopCat.Sheaf.pullback CommRingCat.{u} f.toShHom.hom.base).obj Y.sheaf)
        (RingedSpace.inverseImageStructureSheafUnder f.toShHom)).obj.obj (Opposite.op U) :=
  MvPolynomial.eval₂Hom
    ((((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
        f.toShHom.hom.base).unit.app Y.sheaf).hom.app (Opposite.op V) ≫
      ((TopCat.Sheaf.pullback CommRingCat.{u} f.toShHom.hom.base).obj Y.sheaf).obj.map
        (homOfLE e).op ≫
      (CategoryTheory.Sheaf.FreeAlgebra.Presentation.base
        ((TopCat.Sheaf.pullback CommRingCat.{u} f.toShHom.hom.base).obj Y.sheaf)
        (RingedSpace.inverseImageStructureSheafUnder f.toShHom)).hom.app
          (Opposite.op U)).hom)
    ((CategoryTheory.Sheaf.FreeAlgebra.Presentation.generator
      ((TopCat.Sheaf.pullback CommRingCat.{u} f.toShHom.hom.base).obj Y.sheaf)
      (RingedSpace.inverseImageStructureSheafUnder f.toShHom)).hom.app (Opposite.op U))

/-- The affine polynomial map respects the coefficient-ring map on sections. -/
theorem affinePolynomialMap_C
    {X Y : Scheme.{u}} (f : X ⟶ Y) {U : X.Opens} {V : Y.Opens}
    (e : U ≤ f ⁻¹ᵁ V) (r : Γ(Y, V)) :
    affinePolynomialMap f e (MvPolynomial.C r) =
      ((((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
          f.toShHom.hom.base).unit.app Y.sheaf).hom.app (Opposite.op V) ≫
        ((TopCat.Sheaf.pullback CommRingCat.{u} f.toShHom.hom.base).obj Y.sheaf).obj.map
          (homOfLE e).op ≫
        (CategoryTheory.Sheaf.FreeAlgebra.Presentation.base
          ((TopCat.Sheaf.pullback CommRingCat.{u} f.toShHom.hom.base).obj Y.sheaf)
          (RingedSpace.inverseImageStructureSheafUnder f.toShHom)).hom.app
            (Opposite.op U)).hom r) := sorry

/-- The affine polynomial map respects the canonical integer-algebra structures. -/
theorem affinePolynomialMap_intCast
    {X Y : Scheme.{u}} (f : X ⟶ Y) {U : X.Opens} {V : Y.Opens}
    (e : U ≤ f ⁻¹ᵁ V) (r : ℤ) :
    affinePolynomialMap f e (algebraMap ℤ (MvPolynomial Γ(X, U) Γ(Y, V)) r) =
      algebraMap ℤ
        ((CategoryTheory.Sheaf.FreeAlgebra.Presentation.underlying
          ((TopCat.Sheaf.pullback CommRingCat.{u} f.toShHom.hom.base).obj Y.sheaf)
          (RingedSpace.inverseImageStructureSheafUnder f.toShHom)).obj.obj
            (Opposite.op U)) r := sorry

/-- The canonical affine polynomial map as a morphism of algebras over `Γ(Y, V)`. -/
@[no_expose]
noncomputable def affinePolynomialAlgHom
    {X Y : Scheme.{u}} (f : X ⟶ Y) {U : X.Opens} {V : Y.Opens}
    (e : U ≤ f ⁻¹ᵁ V) :
    MvPolynomial Γ(X, U) Γ(Y, V) →ₐ[ℤ]
      (CategoryTheory.Sheaf.FreeAlgebra.Presentation.underlying
        ((TopCat.Sheaf.pullback CommRingCat.{u} f.toShHom.hom.base).obj Y.sheaf)
        (RingedSpace.inverseImageStructureSheafUnder f.toShHom)).obj.obj (Opposite.op U) :=
  { toRingHom := affinePolynomialMap f e
    commutes' := affinePolynomialMap_intCast f e }

/-- Relations in the affine self-presentation map to relations in the canonical sheaf
presentation on `U`. -/
theorem affinePolynomialMap_mem_conormalIdeal
    {X Y : Scheme.{u}} (f : X ⟶ Y) {U : X.Opens} {V : Y.Opens}
    (e : U ≤ f ⁻¹ᵁ V) :
    RingHom.ker (affineEvaluation f e) ≤
      (conormalIdeal
        (CategoryTheory.Sheaf.FreeAlgebra.Presentation.map
          ((TopCat.Sheaf.pullback CommRingCat.{u} f.toShHom.hom.base).obj Y.sheaf)
          (RingedSpace.inverseImageStructureSheafUnder f.toShHom))
        (Opposite.op U)).comap (affinePolynomialAlgHom f e) := sorry

/-- The image of the top open under the canonical affine presentation of `U` is `U`. -/
theorem affineImageTop
    {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) :
    hU.fromSpec ''ᵁ (⊤ : (Spec (CommRingCat.of Γ(X, U))).Opens) = U := sorry

/-- Transport a section on `U` to a global section of its restriction along `hU.fromSpec`. -/
@[no_expose]
noncomputable def affineSectionAtTop
    {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (M : X.Modules) (x : Γ(M, U)) : Γ(M.restrict hU.fromSpec, ⊤) :=
  (M.restrictAppIso hU.fromSpec ⊤).inv
    (M.presheaf.map (eqToHom (affineImageTop hU)).op x)

/-- The canonical conormal section attached to an element of the lifted affine conormal
module. -/
@[no_expose]
noncomputable def affineConormalSection
    {X Y : Scheme.{u}} (f : X ⟶ Y) {U : X.Opens} {V : Y.Opens}
    (hU : IsAffineOpen U) (e : U ≤ f ⁻¹ᵁ V)
    (x : ((CommRingCat.Hom.naiveCotangent
      (CommRingCat.ofHom (f.sectionsMapAlong V U e))).extend embeddingDownNat).X (-1)) :
    Γ((Scheme.Modules.restrictFunctor hU.fromSpec).obj
      ((RingedSpace.naiveCotangent f.toShHom).X (-1)), ⊤) :=
  -- Local instance justification (defeq pin): the algebraic naive-cotangent component uses exactly the algebra structure induced by `sectionsMapAlong`.
  letI : Algebra Γ(Y, V) Γ(X, U) := (f.sectionsMapAlong V U e).toAlgebra
  let K := CommRingCat.Hom.naiveCotangent
    (CommRingCat.ofHom (f.sectionsMapAlong V U e))
  let P := (Algebra.Generators.self Γ(Y, V) Γ(X, U)).toExtension
  affineSectionAtTop hU ((RingedSpace.naiveCotangent f.toShHom).X (-1))
    ((conormalSourcePresheafUnit
        (CategoryTheory.Sheaf.FreeAlgebra.Presentation.map
          ((TopCat.Sheaf.pullback CommRingCat.{u} f.toShHom.hom.base).obj Y.sheaf)
          (RingedSpace.inverseImageStructureSheafUnder f.toShHom))).app (Opposite.op U)
      (Ideal.mapCotangent (RingHom.ker (affineEvaluation f e))
        (conormalIdeal
          (CategoryTheory.Sheaf.FreeAlgebra.Presentation.map
            ((TopCat.Sheaf.pullback CommRingCat.{u} f.toShHom.hom.base).obj Y.sheaf)
            (RingedSpace.inverseImageStructureSheafUnder f.toShHom))
          (Opposite.op U))
        (affinePolynomialAlgHom f e) (affinePolynomialMap_mem_conormalIdeal f e)
        ((Algebra.Extension.NaiveCotangent.liftEquiv P
          (((K.extendXIso embeddingDownNat rfl).hom ≫
            (Algebra.Extension.NaiveCotangent.componentOneIso P).hom) x)).val)))

/-- The affine conormal-section construction preserves zero. -/
theorem affineConormalSection_zero
    {X Y : Scheme.{u}} (f : X ⟶ Y) {U : X.Opens} {V : Y.Opens}
    (hU : IsAffineOpen U) (e : U ≤ f ⁻¹ᵁ V) :
    affineConormalSection f hU e 0 = 0 := sorry

/-- The affine conormal-section construction preserves addition. -/
theorem affineConormalSection_add
    {X Y : Scheme.{u}} (f : X ⟶ Y) {U : X.Opens} {V : Y.Opens}
    (hU : IsAffineOpen U) (e : U ≤ f ⁻¹ᵁ V)
    (x y : ((CommRingCat.Hom.naiveCotangent
      (CommRingCat.ofHom (f.sectionsMapAlong V U e))).extend embeddingDownNat).X (-1)) :
    affineConormalSection f hU e (x + y) =
      affineConormalSection f hU e x + affineConormalSection f hU e y := sorry

/-- The affine conormal-section construction is linear over `Γ(X, U)`. -/
theorem affineConormalSection_smul
    {X Y : Scheme.{u}} (f : X ⟶ Y) {U : X.Opens} {V : Y.Opens}
    (hU : IsAffineOpen U) (e : U ≤ f ⁻¹ᵁ V) (r : Γ(X, U))
    (x : ((CommRingCat.Hom.naiveCotangent
      (CommRingCat.ofHom (f.sectionsMapAlong V U e))).extend embeddingDownNat).X (-1)) :
    affineConormalSection f hU e (r • x) =
      r • affineConormalSection f hU e x := sorry

/-- The map on affine sections defining the conormal component. -/
@[no_expose]
noncomputable def affineConormalAddHom
    {X Y : Scheme.{u}} (f : X ⟶ Y) {U : X.Opens} {V : Y.Opens}
    (hU : IsAffineOpen U) (e : U ≤ f ⁻¹ᵁ V) :
    (forget₂ (ModuleCat Γ(X, U)) AddCommGrpCat).obj
        (((CommRingCat.Hom.naiveCotangent
          (CommRingCat.ofHom (f.sectionsMapAlong V U e))).extend embeddingDownNat).X (-1)) ⟶
      (forget₂ (ModuleCat Γ(X, U)) AddCommGrpCat).obj
        ((moduleSpecΓFunctor (R := Γ(X, U))).obj
          ((((Scheme.Modules.restrictFunctor hU.fromSpec).mapHomologicalComplex (up ℤ)).obj
            (RingedSpace.naiveCotangent f.toShHom)).X (-1))) :=
  AddCommGrpCat.ofHom
    { toFun := affineConormalSection f hU e
      map_zero' := affineConormalSection_zero f hU e
      map_add' := affineConormalSection_add f hU e
    }

/-- The additive conormal-section map respects the transported affine scalar actions. -/
theorem affineConormalAddHom_smul
    {X Y : Scheme.{u}} (f : X ⟶ Y) {U : X.Opens} {V : Y.Opens}
    (hU : IsAffineOpen U) (e : U ≤ f ⁻¹ᵁ V) (r : Γ(X, U)) :
    affineConormalAddHom f hU e ≫
        ((moduleSpecΓFunctor (R := Γ(X, U))).obj
          ((((Scheme.Modules.restrictFunctor hU.fromSpec).mapHomologicalComplex (up ℤ)).obj
            (RingedSpace.naiveCotangent f.toShHom)).X (-1))).smul r =
      (((CommRingCat.Hom.naiveCotangent
        (CommRingCat.ofHom (f.sectionsMapAlong V U e))).extend embeddingDownNat).X (-1)).smul r ≫
        affineConormalAddHom f hU e := sorry

/-- The conormal-section map as a morphism of modules over `Γ(X, U)`. -/
@[no_expose]
noncomputable def affineConormalSectionsMap
    {X Y : Scheme.{u}} (f : X ⟶ Y) {U : X.Opens} {V : Y.Opens}
    (hU : IsAffineOpen U) (e : U ≤ f ⁻¹ᵁ V) :
    ((CommRingCat.Hom.naiveCotangent
      (CommRingCat.ofHom (f.sectionsMapAlong V U e))).extend embeddingDownNat).X (-1) ⟶
      (moduleSpecΓFunctor (R := Γ(X, U))).obj
        ((((Scheme.Modules.restrictFunctor hU.fromSpec).mapHomologicalComplex (up ℤ)).obj
          (RingedSpace.naiveCotangent f.toShHom)).X (-1)) :=
  ModuleCat.homMk (affineConormalAddHom f hU e)
    (affineConormalAddHom_smul f hU e)

/-- The canonical conormal component of the affine comparison. -/
noncomputable def affineConormalMap
    {X Y : Scheme.{u}} (f : X ⟶ Y) {U : X.Opens} {V : Y.Opens}
    (hU : IsAffineOpen U) (e : U ≤ f ⁻¹ᵁ V) :
    (((tilde.functor (CommRingCat.of Γ(X, U))).mapHomologicalComplex (up ℤ)).obj
      ((CommRingCat.Hom.naiveCotangent
        (CommRingCat.ofHom (f.sectionsMapAlong V U e))).extend embeddingDownNat)).X (-1) ⟶
      (((Scheme.Modules.restrictFunctor hU.fromSpec).mapHomologicalComplex (up ℤ)).obj
        (RingedSpace.naiveCotangent f.toShHom)).X (-1) :=
  (tilde.adjunction.homEquiv _ _).symm
    (affineConormalSectionsMap f hU e)

/-- The canonical degree-zero section associated to an affine coordinate. -/
@[no_expose]
noncomputable def affineDifferentialsSection
    {X Y : Scheme.{u}} (f : X ⟶ Y) {U : X.Opens}
    (hU : IsAffineOpen U) (a : Γ(X, U)) :
    Γ((Scheme.Modules.restrictFunctor hU.fromSpec).obj
      ((RingedSpace.naiveCotangent f.toShHom).X 0), ⊤) :=
  affineSectionAtTop hU ((RingedSpace.naiveCotangent f.toShHom).X 0)
    (((extendRestrictAdj
      (CategoryTheory.Sheaf.FreeAlgebra.Presentation.map
        ((TopCat.Sheaf.pullback CommRingCat.{u} f.toShHom.hom.base).obj Y.sheaf)
        (RingedSpace.inverseImageStructureSheafUnder f.toShHom))).unit.app
          Ω(CategoryTheory.Sheaf.FreeAlgebra.Presentation.base
            ((TopCat.Sheaf.pullback CommRingCat.{u} f.toShHom.hom.base).obj Y.sheaf)
            (RingedSpace.inverseImageStructureSheafUnder f.toShHom))).val.app
              (Opposite.op U)
      (((relativeDifferential
        (CategoryTheory.Sheaf.FreeAlgebra.Presentation.base
          ((TopCat.Sheaf.pullback CommRingCat.{u} f.toShHom.hom.base).obj Y.sheaf)
          (RingedSpace.inverseImageStructureSheafUnder f.toShHom))).app
            (Opposite.op U)).d
        ((CategoryTheory.Sheaf.FreeAlgebra.Presentation.generator
          ((TopCat.Sheaf.pullback CommRingCat.{u} f.toShHom.hom.base).obj Y.sheaf)
          (RingedSpace.inverseImageStructureSheafUnder f.toShHom)).hom.app
            (Opposite.op U) a)))

/-- The additive map on affine sections defining the differential component. -/
@[no_expose]
noncomputable def affineDifferentialsAddHom
    {X Y : Scheme.{u}} (f : X ⟶ Y) {U : X.Opens} {V : Y.Opens}
    (hU : IsAffineOpen U) (e : U ≤ f ⁻¹ᵁ V) :
    (forget₂ (ModuleCat Γ(X, U)) AddCommGrpCat).obj
        ((CommRingCat.Hom.naiveCotangent
          (CommRingCat.ofHom (f.sectionsMapAlong V U e))).X 0) ⟶
      (forget₂ (ModuleCat Γ(X, U)) AddCommGrpCat).obj
        ((moduleSpecΓFunctor (R := Γ(X, U))).obj
          ((((Scheme.Modules.restrictFunctor hU.fromSpec).mapHomologicalComplex (up ℤ)).obj
            (RingedSpace.naiveCotangent f.toShHom)).X 0)) :=
  -- Local instance justification (defeq pin): the canonical coordinate basis is defined using the same algebra structure that `CommRingCat.Hom.naiveCotangent` installs internally.
  letI : Algebra Γ(Y, V) Γ(X, U) := (f.sectionsMapAlong V U e).toAlgebra
  let G := Algebra.Generators.self Γ(Y, V) Γ(X, U)
  let N := (moduleSpecΓFunctor (R := Γ(X, U))).obj
    ((((Scheme.Modules.restrictFunctor hU.fromSpec).mapHomologicalComplex (up ℤ)).obj
      (RingedSpace.naiveCotangent f.toShHom)).X 0)
  -- Local instance justification (defeq pin): use the module structure carried by the global-sections functor as the codomain structure for the basis-defined linear map.
  letI : Module Γ(X, U) N := N.isModule
  let φ : G.toExtension.CotangentSpace →ₗ[Γ(X, U)] N :=
    G.cotangentSpaceBasis.constr Γ(X, U)
      (fun a ↦ (affineDifferentialsSection f hU a : N))
  (forget₂ (ModuleCat Γ(X, U)) AddCommGrpCat).map
      (Algebra.Extension.NaiveCotangent.componentZeroIso G.toExtension).hom ≫
    AddCommGrpCat.ofHom φ.toAddHom

/-- The additive differential-section map respects the transported affine scalar actions. -/
theorem affineDifferentialsAddHom_smul
    {X Y : Scheme.{u}} (f : X ⟶ Y) {U : X.Opens} {V : Y.Opens}
    (hU : IsAffineOpen U) (e : U ≤ f ⁻¹ᵁ V) (r : Γ(X, U)) :
    affineDifferentialsAddHom f hU e ≫
        ((moduleSpecΓFunctor (R := Γ(X, U))).obj
          ((((Scheme.Modules.restrictFunctor hU.fromSpec).mapHomologicalComplex (up ℤ)).obj
            (RingedSpace.naiveCotangent f.toShHom)).X 0)).smul r =
      ((CommRingCat.Hom.naiveCotangent
        (CommRingCat.ofHom (f.sectionsMapAlong V U e))).X 0).smul r ≫
        affineDifferentialsAddHom f hU e := sorry

/-- The map on affine sections defining the differential component. -/
@[no_expose]
noncomputable def affineDifferentialsSectionsMap
    {X Y : Scheme.{u}} (f : X ⟶ Y) {U : X.Opens} {V : Y.Opens}
    (hU : IsAffineOpen U) (e : U ≤ f ⁻¹ᵁ V) :
    ((CommRingCat.Hom.naiveCotangent
      (CommRingCat.ofHom (f.sectionsMapAlong V U e))).extend embeddingDownNat).X 0 ⟶
      (moduleSpecΓFunctor (R := Γ(X, U))).obj
        ((((Scheme.Modules.restrictFunctor hU.fromSpec).mapHomologicalComplex (up ℤ)).obj
          (RingedSpace.naiveCotangent f.toShHom)).X 0) :=
  let K := CommRingCat.Hom.naiveCotangent
    (CommRingCat.ofHom (f.sectionsMapAlong V U e))
  (K.extendXIso embeddingDownNat
      (show embeddingDownNat.f 0 = (0 : ℤ) from rfl)).hom ≫
    ModuleCat.homMk (affineDifferentialsAddHom f hU e)
      (affineDifferentialsAddHom_smul f hU e)

/-- The canonical differential component of the affine comparison. -/
noncomputable def affineDifferentialsMap
    {X Y : Scheme.{u}} (f : X ⟶ Y) {U : X.Opens} {V : Y.Opens}
    (hU : IsAffineOpen U) (e : U ≤ f ⁻¹ᵁ V) :
    (((tilde.functor (CommRingCat.of Γ(X, U))).mapHomologicalComplex (up ℤ)).obj
      ((CommRingCat.Hom.naiveCotangent
        (CommRingCat.ofHom (f.sectionsMapAlong V U e))).extend embeddingDownNat)).X 0 ⟶
      (((Scheme.Modules.restrictFunctor hU.fromSpec).mapHomologicalComplex (up ℤ)).obj
        (RingedSpace.naiveCotangent f.toShHom)).X 0 :=
  (tilde.adjunction.homEquiv _ _).symm
    (affineDifferentialsSectionsMap f hU e)

/-- The explicit components of the affine comparison, supported in degrees `-1` and `0`. -/
@[no_expose]
noncomputable def affineComparisonComponent
    {X Y : Scheme.{u}} (f : X ⟶ Y) {U : X.Opens} {V : Y.Opens}
    (hU : IsAffineOpen U) (e : U ≤ f ⁻¹ᵁ V) :
    ∀ n,
      (((tilde.functor (CommRingCat.of Γ(X, U))).mapHomologicalComplex (up ℤ)).obj
        ((CommRingCat.Hom.naiveCotangent
          (CommRingCat.ofHom (f.sectionsMapAlong V U e))).extend embeddingDownNat)).X n ⟶
      (((Scheme.Modules.restrictFunctor hU.fromSpec).mapHomologicalComplex (up ℤ)).obj
        (RingedSpace.naiveCotangent f.toShHom)).X n
  | Int.negSucc 0 => affineConormalMap f hU e
  | Int.ofNat 0 => affineDifferentialsMap f hU e
  | _ => 0

/-- The two canonical affine components commute with the naive-cotangent differentials. -/
theorem affineComparisonComponent_comm
    {X Y : Scheme.{u}} (f : X ⟶ Y) {U : X.Opens} {V : Y.Opens}
    (hU : IsAffineOpen U) (e : U ≤ f ⁻¹ᵁ V)
    (i j : ℤ) (_ : (up ℤ).Rel i j) :
    affineComparisonComponent f hU e i ≫
        (((Scheme.Modules.restrictFunctor hU.fromSpec).mapHomologicalComplex (up ℤ)).obj
          (RingedSpace.naiveCotangent f.toShHom)).d i j =
      (((tilde.functor (CommRingCat.of Γ(X, U))).mapHomologicalComplex (up ℤ)).obj
        ((CommRingCat.Hom.naiveCotangent
          (CommRingCat.ofHom (f.sectionsMapAlong V U e))).extend embeddingDownNat)).d i j ≫
        affineComparisonComponent f hU e j := sorry

/-- The affine comparison from the tilde of the algebraic naive cotangent complex to the
restriction of the sheaf-level naive cotangent complex. -/
noncomputable def affineComparison
    {X Y : Scheme.{u}} (f : X ⟶ Y) {U : X.Opens} {V : Y.Opens}
    (hU : IsAffineOpen U) (e : U ≤ f ⁻¹ᵁ V) :
      ((tilde.functor (CommRingCat.of Γ(X, U))).mapHomologicalComplex (up ℤ)).obj
          ((CommRingCat.Hom.naiveCotangent
            (CommRingCat.ofHom (f.sectionsMapAlong V U e))).extend embeddingDownNat) ⟶
        ((Scheme.Modules.restrictFunctor hU.fromSpec).mapHomologicalComplex (up ℤ)).obj
          (RingedSpace.naiveCotangent f.toShHom) where
  f := affineComparisonComponent f hU e
  comm' := affineComparisonComponent_comm f hU e

/-- The degree `-1` component of the affine comparison. -/
lemma affineComparison_f_negOne
    {X Y : Scheme.{u}} (f : X ⟶ Y) {U : X.Opens} {V : Y.Opens}
    (hU : IsAffineOpen U) (e : U ≤ f ⁻¹ᵁ V) :
    (affineComparison f hU e).f (-1) = affineConormalMap f hU e := sorry

/-- The degree `0` component of the affine comparison. -/
lemma affineComparison_f_zero
    {X Y : Scheme.{u}} (f : X ⟶ Y) {U : X.Opens} {V : Y.Opens}
    (hU : IsAffineOpen U) (e : U ≤ f ⁻¹ᵁ V) :
    (affineComparison f hU e).f 0 = affineDifferentialsMap f hU e := sorry

end AlgebraicGeometry.Scheme.Hom.NaiveCotangent
