module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Algebra
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Map.Basic
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.CanonicalAlgebra
public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.Degree.GradedPullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.GradedAlgebra
public import ReasLib.AlgebraicGeometry.Scheme.Module.Monoidal
public import ReasLib.AlgebraicGeometry.Scheme.Module.Sections

/-!
# Chosen twists on a projective spectrum

This leaf records an explicit graded-algebra sheaf of twists, its coherent pullbacks, and the
universal comparison attached to a graded ring map. It also provides the canonical Serre-twist
instance from the associated-module construction.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open Scheme.Modules

noncomputable section

universe u

namespace AlgebraicGeometry

section

variable {A B sigma tau : Type u} [CommRing A] [SetLike sigma A] [AddSubgroupClass sigma A]
  [CommRing B] [SetLike tau B] [AddSubgroupClass tau B]
  {calA : Nat -> sigma} {calB : Nat -> tau} [GradedRing calA] [GradedRing calB]

/-- Sections of a chosen twist family pulled back along a morphism into a projective spectrum. -/
abbrev projTwistPullbackSection
    (P : Int -> (Proj calA).Modules)
    {X : Scheme.{u}} (r : X ⟶ Proj calA) (n : Int) (U : (X.Opens)ᵒᵖ) :=
  ((Scheme.Modules.pullback r).obj (P n)).val.obj U

/-- A coherent integral graded algebra of twists on `Proj calA`, together with explicit graded
algebra models for all of its pullbacks and the canonical nonnegative-degree section maps. -/
structure ProjTwistAlgebra (calA : Nat -> sigma) [GradedRing calA] where
  /-- The integral graded algebra sheaf of twists. -/
  algebra : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} (Proj calA).sheaf Int
  /-- Every integral twist is quasi-coherent. -/
  isQuasicoherent : forall d : Int, (algebra.obj d).IsQuasicoherent
  /-- The degree-zero twist is the structure sheaf. -/
  twist_zero : algebra.obj 0 ≅ SheafOfModules.unit (Proj calA).ringCatSheaf
  /-- The degree-zero twist identification carries the graded unit to the structure-sheaf unit. -/
  twist_zero_one : ∀ U : (Proj calA).Opensᵒᵖ,
    ((twist_zero.hom.val.app U).hom) (algebra.one U) =
      ((SheafOfModules.unit (Proj calA).ringCatSheaf).unitHomEquiv (𝟙 _)).1 U
  /-- The canonical section map from each nonnegative graded-ring piece. -/
  sectionMap : forall d : Nat, AddCommGrpCat.of (calA d) ⟶ globalSections (algebra.obj d)
  /-- The degree-zero section map sends the graded unit to the algebra-sheaf unit. -/
  sectionMap_one :
    (sectionMap 0).hom
        (@GradedMonoid.GOne.one Nat (fun n : Nat => calA n) _ _) =
      algebra.one (Opposite.op ⊤)
  /-- The section maps preserve homogeneous multiplication. -/
  sectionMap_mul : ∀ (m n : Nat) (a : calA m) (b : calA n),
    (sectionMap (m + n)).hom ((SetLike.gMul calA).mul a b) =
      algebra.mul (Opposite.op ⊤) (m : Int) (n : Int)
        ((sectionMap m).hom a) ((sectionMap n).hom b)
  /-- A coherent graded algebra model for the pullback along every scheme morphism. -/
  pullbackAlgebra : forall {X : Scheme.{u}} (_ : X ⟶ Proj calA),
    SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} X.sheaf Int
  /-- The coherent graded pullback data for every scheme morphism. -/
  pullbackData : forall {X : Scheme.{u}} (r : X ⟶ Proj calA),
    Scheme.RelativeProjGradedPullback r algebra (pullbackAlgebra r)

namespace ProjTwistAlgebra

/-- Build a coherent twist algebra from a graded algebra sheaf, its section presentation, and
explicit graded algebra models for all pullbacks. -/
noncomputable def ofPullback
    (algebra : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} (Proj calA).sheaf Int)
    (isQuasicoherent : forall d : Int, (algebra.obj d).IsQuasicoherent)
    (twist_zero : algebra.obj 0 ≅ SheafOfModules.unit (Proj calA).ringCatSheaf)
    (twist_zero_one : ∀ U : (Proj calA).Opensᵒᵖ,
      ((twist_zero.hom.val.app U).hom) (algebra.one U) =
        ((SheafOfModules.unit (Proj calA).ringCatSheaf).unitHomEquiv (𝟙 _)).1 U)
    (sectionMap : forall d : Nat, AddCommGrpCat.of (calA d) ⟶ globalSections (algebra.obj d))
    (sectionMap_one :
      (sectionMap 0).hom
          (@GradedMonoid.GOne.one Nat (fun n : Nat => calA n) _ _) =
        algebra.one (Opposite.op ⊤))
    (sectionMap_mul : ∀ (m n : Nat) (a : calA m) (b : calA n),
      (sectionMap (m + n)).hom ((SetLike.gMul calA).mul a b) =
        algebra.mul (Opposite.op ⊤) (m : Int) (n : Int)
          ((sectionMap m).hom a) ((sectionMap n).hom b))
    (pullbackAlgebra : forall {X : Scheme.{u}} (_ : X ⟶ Proj calA),
      SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} X.sheaf Int)
    (pullbackData : forall {X : Scheme.{u}} (r : X ⟶ Proj calA),
      Scheme.RelativeProjGradedPullback r algebra (pullbackAlgebra r)) :
    ProjTwistAlgebra calA where
  algebra := algebra
  isQuasicoherent := isQuasicoherent
  twist_zero := twist_zero
  twist_zero_one := twist_zero_one
  sectionMap := sectionMap
  sectionMap_one := sectionMap_one
  sectionMap_mul := sectionMap_mul
  pullbackAlgebra := pullbackAlgebra
  pullbackData := pullbackData

/-- The canonical coherent twist algebra built from the Serre twisting sheaves. -/
noncomputable def canonical
    {A : Type u} [CommRing A] (calA : Nat → Submodule ℤ A) [GradedAlgebra calA] :
    ProjTwistAlgebra calA := by
  let algebra := Proj.AssociatedModule.CanonicalAlgebra.algebra calA
  let pullbackAlgebra : ∀ {X : Scheme.{u}} (_ : X ⟶ Proj calA),
      SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} X.sheaf Int :=
    fun {X} r ↦ Scheme.Modules.GradedAlgebra.pullback r algebra
  let sectionMap : ∀ d : Nat,
      AddCommGrpCat.of (calA d) ⟶ globalSections (algebra.obj d) :=
    fun d ↦ AddCommGrpCat.ofHom
      { toFun := fun a ↦
          Proj.AssociatedModule.degreeZeroToGlobalSections calA
            (GradedModule.shiftGrading
              (DirectSum.Decomposition.natToIntGrading calA) (d : Int))
            ⟨a, by simpa⟩
        map_zero' := by sorry
        map_add' := by sorry }
  exact
    { algebra := algebra
      isQuasicoherent := by
        intro d
        exact Proj.AssociatedModule.CanonicalAlgebra.algebra_isQuasicoherent calA d
      twist_zero := (asIso (Proj.AssociatedModule.CanonicalAlgebra.unitHom calA)).symm
      twist_zero_one := by sorry
      sectionMap := sectionMap
      sectionMap_one := by sorry
      sectionMap_mul := by sorry
      pullbackAlgebra := pullbackAlgebra
      pullbackData := fun {X} r ↦
        { degreeIso := fun d ↦ Iso.refl _
          pullbackOne := Scheme.Modules.GradedAlgebra.pullbackOne r algebra
          pullbackMul := Scheme.Modules.GradedAlgebra.pullbackMul r algebra
          map_one := by sorry
          map_mul := by sorry } }

/-- The actual integral twist family underlying a coherent twist algebra. -/
abbrev actualTwist (P : ProjTwistAlgebra calA) : Int -> (Proj calA).Modules :=
  P.algebra.obj

/-- The canonical section maps underlying a coherent twist algebra. -/
abbrev actualSectionMap (P : ProjTwistAlgebra calA) :
    forall d : Nat, AddCommGrpCat.of (calA d) ⟶ globalSections (P.actualTwist d) :=
  P.sectionMap

/-- The degreewise pullback identification underlying a coherent twist algebra. -/
abbrev pullbackIso (P : ProjTwistAlgebra calA)
    {X : Scheme.{u}} (r : X ⟶ Proj calA) (d : Int) :
    (Scheme.Modules.pullback r).obj (P.algebra.obj d) ≅ (P.pullbackAlgebra r).obj d :=
  (P.pullbackData r).degreeIso d

/-- The degree-zero unit on a pullback, transported from its coherent graded algebra model. -/
noncomputable def actualOne (P : ProjTwistAlgebra calA)
    {X : Scheme.{u}} (r : X ⟶ Proj calA) (U : (X.Opens)ᵒᵖ) :
    projTwistPullbackSection P.actualTwist r 0 U :=
  (P.pullbackData r).pullbackOne U

/-- Multiplication on pulled-back twists, transported from the coherent graded algebra model. -/
noncomputable def actualMul (P : ProjTwistAlgebra calA)
    {X : Scheme.{u}} (r : X ⟶ Proj calA) (U : (X.Opens)ᵒᵖ) (a b : Int)
    (x : projTwistPullbackSection P.actualTwist r a U)
    (y : projTwistPullbackSection P.actualTwist r b U) :
    projTwistPullbackSection P.actualTwist r (a + b) U :=
  (P.pullbackData r).pullbackMul U a b
    x y

/-- Transport to the coherent pullback model identifies the chosen unit and multiplication with
the graded algebra operations. -/
theorem spec (P : ProjTwistAlgebra calA) :
    (forall d : Int, (P.actualTwist d).IsQuasicoherent) /\
    (forall {X : Scheme.{u}} (r : X ⟶ Proj calA) (U : (X.Opens)ᵒᵖ),
      (((P.pullbackIso r 0).hom.val.app U).hom) (P.actualOne r U) =
        (P.pullbackAlgebra r).one U) /\
    forall {X : Scheme.{u}} (r : X ⟶ Proj calA) (U : (X.Opens)ᵒᵖ) (a b : Int)
      (x : projTwistPullbackSection P.actualTwist r a U)
      (y : projTwistPullbackSection P.actualTwist r b U),
      (((P.pullbackIso r (a + b)).hom.val.app U).hom) (P.actualMul r U a b x y) =
        (P.pullbackAlgebra r).mul U a b
          ((((P.pullbackIso r a).hom.val.app U).hom) x)
          ((((P.pullbackIso r b).hom.val.app U).hom) y) := sorry

end ProjTwistAlgebra

/-- A coherent integral twist algebra on `Proj calA`, equipped with the universal comparison to
the coherent twist algebra on the target of every graded ring map. -/
structure ProjTwistPresentation (calA : Nat -> sigma) [GradedRing calA] where
  /-- The coherent graded algebra of actual twists and its section presentation. -/
  twistAlgebra : ProjTwistAlgebra calA
  /-- The selected degreewise comparison to a coherent target twist algebra. -/
  presentationMap :
    forall {B : Type u} {tau : Type u} [CommRing B] [SetLike tau B] [AddSubgroupClass tau B]
      {calB : Nat -> tau} [GradedRing calB],
      (target : ProjTwistAlgebra calB) -> (psi : calA →+*ᵍ calB) -> forall d : Int,
        (Scheme.Modules.pullback (projMapMap psi)).obj (twistAlgebra.actualTwist d) ⟶
          (Scheme.Modules.pullback (projMapDomain psi).ι).obj
            (target.actualTwist d)
  /-- The selected comparison commutes with the canonical nonnegative-degree section maps. -/
  presentationMap_degree_commutes :
    forall {B : Type u} {tau : Type u} [CommRing B] [SetLike tau B] [AddSubgroupClass tau B]
      {calB : Nat -> tau} [GradedRing calB] (target : ProjTwistAlgebra calB)
      (psi : calA →+*ᵍ calB) (d : Nat),
      twistAlgebra.actualSectionMap d ≫
          globalSectionsPullback (projMapMap psi) (twistAlgebra.actualTwist d) ≫
          globalSectionsMap (presentationMap target psi d) =
        AddCommGrpCat.ofHom (psi.gradedAddHom d) ≫ target.actualSectionMap d ≫
          globalSectionsPullback (projMapDomain psi).ι (target.actualTwist d)
  /-- The selected comparison preserves the coherent degree-zero unit. -/
  presentationMap_map_one :
    forall {B : Type u} {tau : Type u} [CommRing B] [SetLike tau B] [AddSubgroupClass tau B]
      {calB : Nat -> tau} [GradedRing calB] (target : ProjTwistAlgebra calB)
      (psi : calA →+*ᵍ calB) (U : ((projMapDomain psi).toScheme.Opens)ᵒᵖ),
      (((presentationMap target psi 0).val.app U).hom)
          (twistAlgebra.actualOne (projMapMap psi) U) =
        target.actualOne (projMapDomain psi).ι U
  /-- The selected comparison preserves coherent graded multiplication. -/
  presentationMap_map_mul :
    forall {B : Type u} {tau : Type u} [CommRing B] [SetLike tau B] [AddSubgroupClass tau B]
      {calB : Nat -> tau} [GradedRing calB] (target : ProjTwistAlgebra calB)
      (psi : calA →+*ᵍ calB) (U : ((projMapDomain psi).toScheme.Opens)ᵒᵖ) (a b : Int)
      (x : projTwistPullbackSection twistAlgebra.actualTwist (projMapMap psi) a U)
      (y : projTwistPullbackSection twistAlgebra.actualTwist (projMapMap psi) b U),
      (((presentationMap target psi (a + b)).val.app U).hom)
          (twistAlgebra.actualMul (projMapMap psi) U a b x y) =
        target.actualMul (projMapDomain psi).ι U a b
          ((((presentationMap target psi a).val.app U).hom) x)
          ((((presentationMap target psi b).val.app U).hom) y)
  /-- The section and graded-algebra laws uniquely determine the selected comparison. -/
  presentationMap_unique :
    forall {B : Type u} {tau : Type u} [CommRing B] [SetLike tau B] [AddSubgroupClass tau B]
      {calB : Nat -> tau} [GradedRing calB] (target : ProjTwistAlgebra calB)
      (psi : calA →+*ᵍ calB)
      (theta : forall d : Int,
        (Scheme.Modules.pullback (projMapMap psi)).obj (twistAlgebra.actualTwist d) ⟶
          (Scheme.Modules.pullback (projMapDomain psi).ι).obj (target.actualTwist d))
      (h_degree : forall d : Nat,
        twistAlgebra.actualSectionMap d ≫
            globalSectionsPullback (projMapMap psi) (twistAlgebra.actualTwist d) ≫
            globalSectionsMap (theta d) =
          AddCommGrpCat.ofHom (psi.gradedAddHom d) ≫ target.actualSectionMap d ≫
            globalSectionsPullback (projMapDomain psi).ι (target.actualTwist d))
      (h_one : forall U : ((projMapDomain psi).toScheme.Opens)ᵒᵖ,
        (((theta 0).val.app U).hom) (twistAlgebra.actualOne (projMapMap psi) U) =
          target.actualOne (projMapDomain psi).ι U)
      (h_mul : forall (U : ((projMapDomain psi).toScheme.Opens)ᵒᵖ) (a b : Int)
        (x : projTwistPullbackSection twistAlgebra.actualTwist (projMapMap psi) a U)
        (y : projTwistPullbackSection twistAlgebra.actualTwist (projMapMap psi) b U),
        (((theta (a + b)).val.app U).hom)
            (twistAlgebra.actualMul (projMapMap psi) U a b x y) =
          target.actualMul (projMapDomain psi).ι U a b
            ((((theta a).val.app U).hom) x) ((((theta b).val.app U).hom) y)),
      theta = presentationMap target psi

namespace ProjTwistPresentation

/-- Build a universal twist presentation from a coherent source twist algebra and its comparison
maps to coherent target twist algebras. -/
noncomputable def ofTwistAlgebra
    (twistAlgebra : ProjTwistAlgebra calA)
    (presentationMap :
      forall {B : Type u} {tau : Type u} [CommRing B] [SetLike tau B] [AddSubgroupClass tau B]
        {calB : Nat -> tau} [GradedRing calB],
        (target : ProjTwistAlgebra calB) -> (psi : calA →+*ᵍ calB) -> forall d : Int,
          (Scheme.Modules.pullback (projMapMap psi)).obj (twistAlgebra.actualTwist d) ⟶
            (Scheme.Modules.pullback (projMapDomain psi).ι).obj
              (target.actualTwist d))
    (presentationMap_degree_commutes :
      forall {B : Type u} {tau : Type u} [CommRing B] [SetLike tau B] [AddSubgroupClass tau B]
        {calB : Nat -> tau} [GradedRing calB] (target : ProjTwistAlgebra calB)
        (psi : calA →+*ᵍ calB) (d : Nat),
        twistAlgebra.actualSectionMap d ≫
            globalSectionsPullback (projMapMap psi) (twistAlgebra.actualTwist d) ≫
            globalSectionsMap (presentationMap target psi d) =
          AddCommGrpCat.ofHom (psi.gradedAddHom d) ≫ target.actualSectionMap d ≫
            globalSectionsPullback (projMapDomain psi).ι (target.actualTwist d))
    (presentationMap_map_one :
      forall {B : Type u} {tau : Type u} [CommRing B] [SetLike tau B] [AddSubgroupClass tau B]
        {calB : Nat -> tau} [GradedRing calB] (target : ProjTwistAlgebra calB)
        (psi : calA →+*ᵍ calB) (U : ((projMapDomain psi).toScheme.Opens)ᵒᵖ),
        (((presentationMap target psi 0).val.app U).hom)
            (twistAlgebra.actualOne (projMapMap psi) U) =
          target.actualOne (projMapDomain psi).ι U)
    (presentationMap_map_mul :
      forall {B : Type u} {tau : Type u} [CommRing B] [SetLike tau B] [AddSubgroupClass tau B]
        {calB : Nat -> tau} [GradedRing calB] (target : ProjTwistAlgebra calB)
        (psi : calA →+*ᵍ calB) (U : ((projMapDomain psi).toScheme.Opens)ᵒᵖ) (a b : Int)
        (x : projTwistPullbackSection twistAlgebra.actualTwist (projMapMap psi) a U)
        (y : projTwistPullbackSection twistAlgebra.actualTwist (projMapMap psi) b U),
        (((presentationMap target psi (a + b)).val.app U).hom)
            (twistAlgebra.actualMul (projMapMap psi) U a b x y) =
          target.actualMul (projMapDomain psi).ι U a b
            ((((presentationMap target psi a).val.app U).hom) x)
            ((((presentationMap target psi b).val.app U).hom) y))
    (presentationMap_unique :
      forall {B : Type u} {tau : Type u} [CommRing B] [SetLike tau B] [AddSubgroupClass tau B]
        {calB : Nat -> tau} [GradedRing calB] (target : ProjTwistAlgebra calB)
        (psi : calA →+*ᵍ calB)
        (theta : forall d : Int,
          (Scheme.Modules.pullback (projMapMap psi)).obj (twistAlgebra.actualTwist d) ⟶
            (Scheme.Modules.pullback (projMapDomain psi).ι).obj (target.actualTwist d))
        (h_degree : forall d : Nat,
          twistAlgebra.actualSectionMap d ≫
              globalSectionsPullback (projMapMap psi) (twistAlgebra.actualTwist d) ≫
              globalSectionsMap (theta d) =
            AddCommGrpCat.ofHom (psi.gradedAddHom d) ≫ target.actualSectionMap d ≫
              globalSectionsPullback (projMapDomain psi).ι (target.actualTwist d))
        (h_one : forall U : ((projMapDomain psi).toScheme.Opens)ᵒᵖ,
          (((theta 0).val.app U).hom) (twistAlgebra.actualOne (projMapMap psi) U) =
            target.actualOne (projMapDomain psi).ι U)
        (h_mul : forall (U : ((projMapDomain psi).toScheme.Opens)ᵒᵖ) (a b : Int)
          (x : projTwistPullbackSection twistAlgebra.actualTwist (projMapMap psi) a U)
          (y : projTwistPullbackSection twistAlgebra.actualTwist (projMapMap psi) b U),
          (((theta (a + b)).val.app U).hom)
              (twistAlgebra.actualMul (projMapMap psi) U a b x y) =
            target.actualMul (projMapDomain psi).ι U a b
              ((((theta a).val.app U).hom) x) ((((theta b).val.app U).hom) y)),
        theta = presentationMap target psi) :
    ProjTwistPresentation calA where
  twistAlgebra := twistAlgebra
  presentationMap := presentationMap
  presentationMap_degree_commutes := presentationMap_degree_commutes
  presentationMap_map_one := presentationMap_map_one
  presentationMap_map_mul := presentationMap_map_mul
  presentationMap_unique := presentationMap_unique

/-- The actual twist family recorded by a chosen presentation. -/
abbrev actualTwist (P : ProjTwistPresentation calA) : Int -> (Proj calA).Modules :=
  P.twistAlgebra.actualTwist

/-- The tensor twist of a module by an actual integral twist from `P`. -/
abbrev tensorTwist (P : ProjTwistPresentation calA) (F : (Proj calA).Modules) (d : Int) :
    (Proj calA).Modules :=
  tensorObj F (P.actualTwist d)

/-- The defining tensor expression for `ProjTwistPresentation.tensorTwist`. -/
theorem tensorTwist_def (P : ProjTwistPresentation calA) (F : (Proj calA).Modules) (d : Int) :
    P.tensorTwist F d = tensorObj F (P.actualTwist d) := sorry

/-- The canonical section map recorded by a chosen actual-twist presentation. -/
abbrev actualSectionMap (P : ProjTwistPresentation calA) :
    forall d : Nat, AddCommGrpCat.of (calA d) ⟶ globalSections (P.actualTwist d) :=
  P.twistAlgebra.actualSectionMap

/-- The degree-zero unit section recorded by a chosen actual-twist presentation. -/
abbrev actualOne (P : ProjTwistPresentation calA) :
    forall {X : Scheme.{u}} (r : X ⟶ Proj calA) (U : (X.Opens)ᵒᵖ),
      projTwistPullbackSection P.actualTwist r 0 U :=
  P.twistAlgebra.actualOne

/-- The graded multiplication recorded by a chosen actual-twist presentation. -/
abbrev actualMul (P : ProjTwistPresentation calA) :
    forall {X : Scheme.{u}} (r : X ⟶ Proj calA) (U : (X.Opens)ᵒᵖ) (a b : Int),
      projTwistPullbackSection P.actualTwist r a U ->
        projTwistPullbackSection P.actualTwist r b U ->
          projTwistPullbackSection P.actualTwist r (a + b) U :=
  P.twistAlgebra.actualMul

/-- The universal comparison preserves sections, the degree-zero unit, and graded
multiplication for one coherent target twist algebra. -/
theorem spec (P : ProjTwistPresentation calA)
    {B : Type u} {tau : Type u} [CommRing B] [SetLike tau B] [AddSubgroupClass tau B]
    {calB : Nat -> tau} [GradedRing calB] (target : ProjTwistAlgebra calB)
    (psi : calA →+*ᵍ calB) :
    (forall d : Nat,
      P.actualSectionMap d ≫ globalSectionsPullback (projMapMap psi) (P.actualTwist d) ≫
          globalSectionsMap (P.presentationMap target psi d) =
        AddCommGrpCat.ofHom (psi.gradedAddHom d) ≫ target.actualSectionMap d ≫
          globalSectionsPullback (projMapDomain psi).ι (target.actualTwist d)) /\
    (forall U : ((projMapDomain psi).toScheme.Opens)ᵒᵖ,
      (((P.presentationMap target psi 0).val.app U).hom)
          (P.actualOne (projMapMap psi) U) =
        target.actualOne (projMapDomain psi).ι U) /\
    forall (U : ((projMapDomain psi).toScheme.Opens)ᵒᵖ) (a b : Int)
      (x : projTwistPullbackSection P.actualTwist (projMapMap psi) a U)
      (y : projTwistPullbackSection P.actualTwist (projMapMap psi) b U),
      (((P.presentationMap target psi (a + b)).val.app U).hom)
          (P.actualMul (projMapMap psi) U a b x y) =
        target.actualMul (projMapDomain psi).ι U a b
          ((((P.presentationMap target psi a).val.app U).hom) x)
          ((((P.presentationMap target psi b).val.app U).hom) y) := sorry

end ProjTwistPresentation

/-- The degree-`n` source twist pulled back to the domain of a graded map. -/
abbrev pulledBackProjTwist
    (PcalA : ProjTwistPresentation calA) (psi : calA →+*ᵍ calB)
    (r : (projMapDomain psi).toScheme ⟶ Proj calA) (n : Int) :
    (projMapDomain psi).toScheme.Modules :=
  (Scheme.Modules.pullback r).obj (PcalA.actualTwist n)

/-- The degree-`n` target twist restricted to the domain of a graded map. -/
abbrev restrictedProjTwist
    (PcalB : ProjTwistPresentation calB) (psi : calA →+*ᵍ calB) (n : Int) :
    (projMapDomain psi).toScheme.Modules :=
  (Scheme.Modules.pullback (projMapDomain psi).ι).obj (PcalB.actualTwist n)

/-- Sections of a pulled-back source twist over an open of the map domain. -/
abbrev pulledBackProjTwistSection
    (PcalA : ProjTwistPresentation calA) (psi : calA →+*ᵍ calB)
    (r : (projMapDomain psi).toScheme ⟶ Proj calA) (n : Int)
    (U : ((projMapDomain psi).toScheme.Opens)ᵒᵖ) :=
  (pulledBackProjTwist PcalA psi r n).val.obj U

/-- Sections of a restricted target twist over an open of the map domain. -/
abbrev restrictedProjTwistSection
    (PcalB : ProjTwistPresentation calB) (psi : calA →+*ᵍ calB) (n : Int)
    (U : ((projMapDomain psi).toScheme.Opens)ᵒᵖ) :=
  (restrictedProjTwist PcalB psi n).val.obj U

/-- The degreewise comparison morphism induced by two chosen twist presentations and a graded
ring map. -/
abbrev projMapTheta
    (PcalA : ProjTwistPresentation calA)
    (PcalB : ProjTwistPresentation calB)
    (psi : calA →+*ᵍ calB)
    (d : Int) :
    (Scheme.Modules.pullback (projMapMap psi)).obj (PcalA.actualTwist d) ⟶
      (Scheme.Modules.pullback (projMapDomain psi).ι).obj (PcalB.actualTwist d) :=
  PcalA.presentationMap PcalB.twistAlgebra psi d

end

end AlgebraicGeometry
