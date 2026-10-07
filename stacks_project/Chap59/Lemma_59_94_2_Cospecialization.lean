module

public import stacks_project.Chap59.Lemma_59_94_1
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.CommSq

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.Functor.RightDerived
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale
open AlgebraicGeometry.Scheme.EtaleVanishingCycles
open DerivedCategory.TStructure Opposite

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.EtaleVanishingCycles

variable {X S : Scheme.{u}} (f : X ⟶ S) (sbar : GeometricPoint S)
variable (Rsh : Type u) [CommRing Rsh]
variable [Algebra (S.presheaf.stalk sbar.image) Rsh]
variable [IsStrictHenselizationOf (S.presheaf.stalk sbar.image) Rsh]
variable (tbar : GeometricPoint (strictHenselizationScheme S sbar Rsh))
variable (iS : Spec (.of sbar.K) ⟶ strictHenselizationScheme S sbar Rsh)
variable (hiS : iS ≫ strictHenselizationMap S sbar Rsh = sbar.hom)
variable [QuasiCompact f] [QuasiSeparated f]
variable
    [((smallEtalePullback (cospecializationH f sbar Rsh tbar)).sheafPushforwardContinuous
        AddCommGrpCat.{u + 1} (henselizedFiber f sbar Rsh).smallEtaleTopology
        (pullback (pullback.snd f (strictHenselizationMap S sbar Rsh))
          tbar.hom).smallEtaleTopology).IsRightAdjoint]
    [HasRightDerivedFunctor
      (Cochain.toDerived (directImage (cospecializationH f sbar Rsh tbar)))
      (HomologicalComplex.quasiIso
        (Coefficients
          (pullback (pullback.snd f (strictHenselizationMap S sbar Rsh)) tbar.hom))
        (ComplexShape.up ℤ))]

/-- Restriction of `K` to the henselized fibre `Xsh`. -/
abbrev restrictToHenselizedFiber (K : Complexes X) :
    Complexes (henselizedFiber f sbar Rsh) :=
  (derivedInverseImage (henselizedFiberToX f sbar Rsh)).obj K

/-- Restriction of `K` to the geometric fibre `X_tbar`. -/
abbrev restrictToGeometricFiberT (K : Complexes X) :
    Complexes
      (pullback (pullback.snd f (strictHenselizationMap S sbar Rsh)) tbar.hom) :=
  (derivedInverseImage (cospecializationH f sbar Rsh tbar)).obj
    (restrictToHenselizedFiber f sbar Rsh K)

/-- Restriction of `K` to the geometric fibre `X_sbar`. -/
abbrev restrictToGeometricFiberS (K : Complexes X) :
    Complexes (pullback f sbar.hom) :=
  (derivedInverseImage (cospecializationI f sbar Rsh iS hiS)).obj
    (restrictToHenselizedFiber f sbar Rsh K)

/-- The morphism `X_tbar ⟶ X`. -/
abbrev geometricFiberTToX :
    pullback (pullback.snd f (strictHenselizationMap S sbar Rsh)) tbar.hom ⟶ X :=
  cospecializationH f sbar Rsh tbar ≫ henselizedFiberToX f sbar Rsh

/-- Derived sections of the inverse image of `K` along a morphism into `X`. -/
def geometricFiberSections {Y : Scheme.{u}} (g : Y ⟶ X) (K : Complexes X) :
    DerivedCategory AddCommGrpCat.{u + 1} :=
  (derivedSections Y).obj ((derivedInverseImage g).obj K)

/-- Geometric-fibre sections are derived sections of the inverse image. -/
theorem geometricFiberSections_eq {Y : Scheme.{u}} (g : Y ⟶ X) (K : Complexes X) :
    geometricFiberSections g K =
      (derivedSections Y).obj ((derivedInverseImage g).obj K) :=
  rfl

/-- The object `(Rf_* K)_sbar`, identified via Theorem 59.53.1 with
`RΓ(Xsh, K|_{Xsh})`. -/
def pushforwardStalkS (K : Complexes X) :
    DerivedCategory AddCommGrpCat.{u + 1} :=
  (derivedSections (henselizedFiber f sbar Rsh)).obj
    (restrictToHenselizedFiber f sbar Rsh K)

/-- The stalk object at `sbar` is henselized derived sections of `K`. -/
theorem pushforwardStalkS_eq (K : Complexes X) :
    pushforwardStalkS f sbar Rsh K =
      (derivedSections (henselizedFiber f sbar Rsh)).obj
        (restrictToHenselizedFiber f sbar Rsh K) :=
  rfl

/-- The object `(Rf_* K)_tbar` in the §59.94 reduction, as
`RΓ(Xsh, Rh_*(K|_{X_tbar}))`. -/
def pushforwardStalkT (K : Complexes X) :
    DerivedCategory AddCommGrpCat.{u + 1} :=
  (derivedSections (henselizedFiber f sbar Rsh)).obj
    ((derivedDirectImage (cospecializationH f sbar Rsh tbar)).obj
      (restrictToGeometricFiberT f sbar Rsh tbar K))

/-- The stalk object at `tbar` is derived sections of `Rh_*(K|_{X_tbar})`. -/
theorem pushforwardStalkT_eq (K : Complexes X) :
    pushforwardStalkT f sbar Rsh tbar K =
      (derivedSections (henselizedFiber f sbar Rsh)).obj
        ((derivedDirectImage (cospecializationH f sbar Rsh tbar)).obj
          (restrictToGeometricFiberT f sbar Rsh tbar K)) :=
  rfl

/-- Specialization `sp : (Rf_* K)_sbar ⟶ (Rf_* K)_tbar`, as `RΓ(β)`. -/
def derivedPushforwardSpecialization (K : Complexes X) :
    pushforwardStalkS f sbar Rsh K ⟶ pushforwardStalkT f sbar Rsh tbar K :=
  (derivedSections (henselizedFiber f sbar Rsh)).map
    (etaleCohomologyBeta f sbar Rsh tbar K)

/-- Specialization is derived sections of `β_{K,sbar,tbar}`. -/
theorem derivedPushforwardSpecialization_eq (K : Complexes X) :
    derivedPushforwardSpecialization f sbar Rsh tbar K =
      (derivedSections (henselizedFiber f sbar Rsh)).map
        (etaleCohomologyBeta f sbar Rsh tbar K) :=
  rfl

/-- The terminal étale object of the source is isomorphic to the pullback of the
terminal étale object of the target. -/
instance isIso_unitToPullback {Y Z : Scheme.{u}} (g : Y ⟶ Z) :
    IsIso (unitToPullback g) := sorry

/-- Sheaf-level identification `Γ(Z, g_* F) ⟶ Γ(Y, F)`. -/
def sectionsDirectImageHom {Y Z : Scheme.{u}} (g : Y ⟶ Z) (F : Coefficients Y) :
    (sections Z).obj ((directImage g).obj F) ⟶ (sections Y).obj F :=
  ((sheafPushforwardContinuousCompSheafToPresheafIso
        (smallEtalePullback g) AddCommGrpCat.{u + 1}
        Z.smallEtaleTopology Y.smallEtaleTopology).hom.app F).app
      (Opposite.op (unitObject Z)) ≫
    F.obj.map (unitToPullback g).op

/-- Reverse sheaf-level identification `Γ(Y, F) ⟶ Γ(Z, g_* F)`. -/
def sectionsDirectImageInv {Y Z : Scheme.{u}} (g : Y ⟶ Z) (F : Coefficients Y) :
    (sections Y).obj F ⟶ (sections Z).obj ((directImage g).obj F) :=
  F.obj.map (inv (unitToPullback g).op) ≫
    ((sheafPushforwardContinuousCompSheafToPresheafIso
        (smallEtalePullback g) AddCommGrpCat.{u + 1}
        Z.smallEtaleTopology Y.smallEtaleTopology).inv.app F).app
      (Opposite.op (unitObject Z))

/-- Sheaf-level identification `Γ(Z, g_* F) ≅ Γ(Y, F)`. -/
def sectionsDirectImageIso {Y Z : Scheme.{u}} (g : Y ⟶ Z) (F : Coefficients Y) :
    (sections Z).obj ((directImage g).obj F) ≅ (sections Y).obj F where
  hom := sectionsDirectImageHom g F
  inv := sectionsDirectImageInv g F
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Natural sheaf-level identification `Γ(Z, g_* (-)) ≅ Γ(Y, -)`. -/
def sectionsDirectImageNatIso {Y Z : Scheme.{u}} (g : Y ⟶ Z) :
    directImage g ⋙ sections Z ≅ sections Y :=
  NatIso.ofComponents (fun F => sectionsDirectImageIso g F)
    (fun {F G} (_φ : F ⟶ G) => sorry)

/-- Derived comparison `RΓ(Y, M) ⟶ RΓ(Z, Rg_* M)`. -/
def derivedSectionsDirectImageInv {Y Z : Scheme.{u}} (g : Y ⟶ Z)
    [HasRightDerivedFunctor (Cochain.toDerived (directImage g))
      (HomologicalComplex.quasiIso (Coefficients Y) (ComplexShape.up ℤ))] :
    derivedSections Y ⟶ derivedDirectImage g ⋙ derivedSections Z :=
  (derivedSections Y).rightDerivedDesc
    (Cochain.unit (sections Y))
    (HomologicalComplex.quasiIso (Coefficients Y) (ComplexShape.up ℤ))
    (derivedDirectImage g ⋙ derivedSections Z)
    (Functor.whiskerRight
      (NatTrans.mapHomologicalComplex (sectionsDirectImageNatIso g).inv
        (ComplexShape.up ℤ))
      (DerivedCategory.Q : CochainComplex AddCommGrpCat.{u + 1} ℤ ⥤
        DerivedCategory AddCommGrpCat.{u + 1}) ≫
      Functor.whiskerRight
        (Functor.mapHomologicalComplexCompIso (Iso.refl (directImage g ⋙ sections Z))
          (ComplexShape.up ℤ)).hom
        (DerivedCategory.Q : CochainComplex AddCommGrpCat.{u + 1} ℤ ⥤
          DerivedCategory AddCommGrpCat.{u + 1}) ≫
      (Functor.associator
        ((directImage g).mapHomologicalComplex (ComplexShape.up ℤ))
        ((sections Z).mapHomologicalComplex (ComplexShape.up ℤ))
        (DerivedCategory.Q : CochainComplex AddCommGrpCat.{u + 1} ℤ ⥤
          DerivedCategory AddCommGrpCat.{u + 1})).hom ≫
      Functor.whiskerLeft
        ((directImage g).mapHomologicalComplex (ComplexShape.up ℤ))
        (Cochain.unit (sections Z)) ≫
      (Functor.associator
        ((directImage g).mapHomologicalComplex (ComplexShape.up ℤ))
        (DerivedCategory.Q : CochainComplex (Coefficients Z) ℤ ⥤ Complexes Z)
        (derivedSections Z)).inv ≫
      Functor.whiskerRight (Cochain.unit (directImage g)) (derivedSections Z) ≫
      (Functor.associator
        (DerivedCategory.Q : CochainComplex (Coefficients Y) ℤ ⥤ Complexes Y)
        (derivedDirectImage g)
        (derivedSections Z)).inv)

/-- Derived comparison `RΓ(Z, Rg_* M) ⟶ RΓ(Y, M)` is inverse to the comparison
induced by sheaf-level identification. -/
instance derivedSectionsDirectImageInv_isIso {Y Z : Scheme.{u}} (g : Y ⟶ Z)
    [HasRightDerivedFunctor (Cochain.toDerived (directImage g))
      (HomologicalComplex.quasiIso (Coefficients Y) (ComplexShape.up ℤ))] :
    IsIso (derivedSectionsDirectImageInv g) := sorry

/-- Derived comparison `RΓ(Z, Rg_* M) ⟶ RΓ(Y, M)`. -/
def derivedSectionsDirectImageHom {Y Z : Scheme.{u}} (g : Y ⟶ Z)
    [HasRightDerivedFunctor (Cochain.toDerived (directImage g))
      (HomologicalComplex.quasiIso (Coefficients Y) (ComplexShape.up ℤ))] :
    derivedDirectImage g ⋙ derivedSections Z ⟶ derivedSections Y :=
  inv (derivedSectionsDirectImageInv g)

/-- Derived identification `RΓ(Z, Rg_* M) ≅ RΓ(Y, M)`. -/
def derivedSectionsDirectImageIso {Y Z : Scheme.{u}} (g : Y ⟶ Z)
    [HasRightDerivedFunctor (Cochain.toDerived (directImage g))
      (HomologicalComplex.quasiIso (Coefficients Y) (ComplexShape.up ℤ))] :
    derivedDirectImage g ⋙ derivedSections Z ≅ derivedSections Y :=
  (asIso (derivedSectionsDirectImageInv g)).symm

/-- The base-change map `(Rf_* K)_tbar ⟶ RΓ(X_tbar, K)`. -/
def pushforwardStalkToGeometricFiberT (K : Complexes X) :
    pushforwardStalkT f sbar Rsh tbar K ⟶
      (derivedSections
          (pullback (pullback.snd f (strictHenselizationMap S sbar Rsh)) tbar.hom)).obj
        (restrictToGeometricFiberT f sbar Rsh tbar K) :=
  (derivedSectionsDirectImageIso (cospecializationH f sbar Rsh tbar)).hom.app
    (restrictToGeometricFiberT f sbar Rsh tbar K)

/-- The base-change map is the derived sections identification along `h`. -/
theorem pushforwardStalkToGeometricFiberT_eq (K : Complexes X) :
    pushforwardStalkToGeometricFiberT f sbar Rsh tbar K =
      (derivedSectionsDirectImageIso (cospecializationH f sbar Rsh tbar)).hom.app
        (restrictToGeometricFiberT f sbar Rsh tbar K) :=
  rfl

/-- The comparison `(Rf_* K)_sbar ⟶ RΓ(X_sbar, K)`, as derived restriction along `i`. -/
def pushforwardStalkToGeometricFiberS (K : Complexes X) :
    pushforwardStalkS f sbar Rsh K ⟶
      (derivedSections (pullback f sbar.hom)).obj
        (restrictToGeometricFiberS f sbar Rsh iS hiS K) :=
  (derivedSectionsPullback (cospecializationI f sbar Rsh iS hiS)).app
    (restrictToHenselizedFiber f sbar Rsh K)

/-- The comparison at `sbar` is derived restriction along `i`. -/
theorem pushforwardStalkToGeometricFiberS_eq (K : Complexes X) :
    pushforwardStalkToGeometricFiberS f sbar Rsh iS hiS K =
      (derivedSectionsPullback (cospecializationI f sbar Rsh iS hiS)).app
        (restrictToHenselizedFiber f sbar Rsh K) :=
  rfl

variable (K : Complexes X) (hK : t.plus K) [LocallyAcyclicRelative f K]

/-- Inverse of `i⁻¹ β_{K,sbar,tbar}` from Lemma 59.94.1. -/
def inverseImageBetaInv :
    (derivedInverseImage (cospecializationI f sbar Rsh iS hiS)).obj
        ((derivedDirectImage (cospecializationH f sbar Rsh tbar)).obj
          (restrictToGeometricFiberT f sbar Rsh tbar K)) ⟶
      restrictToGeometricFiberS f sbar Rsh iS hiS K :=
  @CategoryTheory.inv _ _ _ _
    ((derivedInverseImage (cospecializationI f sbar Rsh iS hiS)).map
      (etaleCohomologyBeta f sbar Rsh tbar K))
    (isIso_inverseImage_etaleCohomologyBeta f sbar Rsh tbar iS hiS K hK)

/-- The cospecialization map `cosp : RΓ(X_tbar, K) ⟶ RΓ(X_sbar, K)`. -/
def cospecializationMap :
    (derivedSections
        (pullback (pullback.snd f (strictHenselizationMap S sbar Rsh)) tbar.hom)).obj
      (restrictToGeometricFiberT f sbar Rsh tbar K) ⟶
      (derivedSections (pullback f sbar.hom)).obj
        (restrictToGeometricFiberS f sbar Rsh iS hiS K) :=
  (derivedSectionsDirectImageIso (cospecializationH f sbar Rsh tbar)).inv.app
      (restrictToGeometricFiberT f sbar Rsh tbar K) ≫
    (derivedSectionsPullback (cospecializationI f sbar Rsh iS hiS)).app
      ((derivedDirectImage (cospecializationH f sbar Rsh tbar)).obj
        (restrictToGeometricFiberT f sbar Rsh tbar K)) ≫
    (derivedSections (pullback f sbar.hom)).map
      (inverseImageBetaInv f sbar Rsh tbar iS hiS K hK)

/-- Cospecialization inverts `RΓ(Xsh, Rh_*) ≅ RΓ(X_tbar)`, pulls back along `i`,
and applies the inverse of `i⁻¹ β`. -/
theorem cospecializationMap_eq :
    cospecializationMap f sbar Rsh tbar iS hiS K hK =
      (derivedSectionsDirectImageIso (cospecializationH f sbar Rsh tbar)).inv.app
          (restrictToGeometricFiberT f sbar Rsh tbar K) ≫
        (derivedSectionsPullback (cospecializationI f sbar Rsh iS hiS)).app
          ((derivedDirectImage (cospecializationH f sbar Rsh tbar)).obj
            (restrictToGeometricFiberT f sbar Rsh tbar K)) ≫
        (derivedSections (pullback f sbar.hom)).map
          (inverseImageBetaInv f sbar Rsh tbar iS hiS K hK) :=
  rfl

end AlgebraicGeometry.Scheme.EtaleVanishingCycles
