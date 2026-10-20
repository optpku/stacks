module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommInvariants
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.CompactSupportCoinvariants
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import Mathlib.CategoryTheory.Sites.LeftExact

/-!
# Natural comparisons for cohomology of curves

Geometric global sections and compactly supported cohomology of finite locally
constant sheaves are compared with geometric invariants and twisted coinvariants.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale
open AlgebraicGeometry.SchemeOverField
open CategoryTheory.Action.ModuleCat
open CategoryTheory.ObjectProperty
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]
variable (X : SchemeOverField k)
variable [hCurve : Curve X] [hSmooth : Smooth X.hom] [hConnected : GeometricallyConnected X.hom]
variable [ConnectedSpace X.left] [ConnectedSpace (geometricBaseChange X)]
variable {Λ : Type (u + 1)} [Ring Λ] [Finite Λ]
variable (ηbar : GeometricPoint (geometricBaseChange X))
variable [HasWeakSheafify X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
variable [∀ U : X.left.Etale,
    HasWeakSheafify ((X.left.smallEtaleTopology).over U) (ModuleCat.{u + 1} Λ)]
variable [HasWeakSheafify (geometricBaseChange X).smallEtaleTopology (ModuleCat.{u + 1} Λ)]
variable [∀ P : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
    (smallEtalePullback (geometricToArithmeticHom X)).op.HasLeftKanExtension P]
variable [(X.left.smallEtaleTopology).HasSheafCompose
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})]
variable (M : (finiteTypeDiscreteModule Λ
    (Aut (GeometricPoint.finiteFiber (arithmeticPoint X ηbar)))).FullSubcategory)

omit hCurve hSmooth hConnected

/-- Global sections of the geometric pullback of the sheaf associated to a finite
arithmetic fundamental-group module. -/
def geometricH0Module : ModuleCat.{u + 1} Λ :=
  (((smallEtalePullback (geometricToArithmeticHom X)).sheafPullback
      (ModuleCat.{u + 1} Λ) X.left.smallEtaleTopology
      (geometricBaseChange X).smallEtaleTopology).obj
    (associatedSheaf Λ (arithmeticPoint X ηbar) M)).obj.obj
      (Opposite.op (globalEtale (geometricBaseChange X)))

/-- The map on geometric global sections obtained by pulling back and evaluating the
associated sheaf morphism of a coefficient map. -/
def geometricH0Map
    {N : (finiteTypeDiscreteModule Λ
        (Aut (GeometricPoint.finiteFiber (arithmeticPoint X ηbar)))).FullSubcategory}
    (f : M ⟶ N) : geometricH0Module X ηbar M ⟶ geometricH0Module X ηbar N :=
  (((smallEtalePullback (geometricToArithmeticHom X)).sheafPullback
      (ModuleCat.{u + 1} Λ) X.left.smallEtaleTopology
      (geometricBaseChange X).smallEtaleTopology).map
    ((associatedSheafFunctor Λ (arithmeticPoint X ηbar)).map f)).hom.app
      (Opposite.op (globalEtale (geometricBaseChange X)))

/-- Geometric `π₁(X_k̄, η̄)`-invariants of `M`, as a `Λ`-module. -/
abbrev geometricPi1Invariants : ModuleCat.{u + 1} Λ :=
  (NoncommInvariants.functor Λ (Aut (GeometricPoint.finiteFiber ηbar))).obj
    (geometricRestriction X ηbar M.obj)

omit [ConnectedSpace X.left] [Finite Λ]
  [HasWeakSheafify X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
  [∀ U : X.left.Etale,
    HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
  [HasWeakSheafify (geometricBaseChange X).smallEtaleTopology (ModuleCat.{u + 1} Λ)]
  [∀ G : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
    (smallEtalePullback (geometricToArithmeticHom X)).op.HasLeftKanExtension G]
  [X.left.smallEtaleTopology.HasSheafCompose
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})] in
/-- Unfolding of geometric `π₁`-invariants as the fixed-vector functor of the geometric
restriction. -/
theorem geometricPi1Invariants_eq :
    geometricPi1Invariants X ηbar M =
      (NoncommInvariants.functor Λ (Aut (GeometricPoint.finiteFiber ηbar))).obj
        (geometricRestriction X ηbar M.obj) :=
  rfl

/-- The map on geometric `π₁`-invariants induced by a morphism of representations. -/
def geometricPi1InvariantsMap
    {N : (finiteTypeDiscreteModule Λ
        (Aut (GeometricPoint.finiteFiber (arithmeticPoint X ηbar)))).FullSubcategory}
    (f : M ⟶ N) :
    geometricPi1Invariants X ηbar M ⟶ geometricPi1Invariants X ηbar N :=
  (NoncommInvariants.functor Λ (Aut (GeometricPoint.finiteFiber ηbar))).map
    ((discreteModuleRes (geometricToArithmetic X ηbar).hom).map f.hom)

omit [ConnectedSpace X.left] [Finite Λ]
  [HasWeakSheafify X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
  [∀ U : X.left.Etale,
    HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
  [HasWeakSheafify (geometricBaseChange X).smallEtaleTopology (ModuleCat.{u + 1} Λ)]
  [∀ G : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
    (smallEtalePullback (geometricToArithmeticHom X)).op.HasLeftKanExtension G]
  [X.left.smallEtaleTopology.HasSheafCompose
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})] in
/-- Unfolding of the induced map on geometric `π₁`-invariants. -/
theorem geometricPi1InvariantsMap_eq
    {N : (finiteTypeDiscreteModule Λ
        (Aut (GeometricPoint.finiteFiber (arithmeticPoint X ηbar)))).FullSubcategory}
    (f : M ⟶ N) :
    geometricPi1InvariantsMap X ηbar M f =
      (NoncommInvariants.functor Λ (Aut (GeometricPoint.finiteFiber ηbar))).map
        ((discreteModuleRes (geometricToArithmetic X ηbar).hom).map f.hom) :=
  rfl

omit [X.left.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})] in
include hCurve hSmooth hConnected in
/-- On a smooth geometrically connected projective curve, geometric global sections
are naturally isomorphic to geometric fundamental-group invariants. -/
theorem geometricH0_iso_pi1Invariants_natural [Projective X.hom] :
    ∃ i : ∀ M : (finiteTypeDiscreteModule Λ
        (Aut (GeometricPoint.finiteFiber (arithmeticPoint X ηbar)))).FullSubcategory,
        geometricH0Module X ηbar M ≅ geometricPi1Invariants X ηbar M,
      ∀ (M N : (finiteTypeDiscreteModule Λ
        (Aut (GeometricPoint.finiteFiber (arithmeticPoint X ηbar)))).FullSubcategory) (f : M ⟶ N),
        (i M).hom ≫ geometricPi1InvariantsMap X ηbar M f =
          geometricH0Map X ηbar M f ≫ (i N).hom :=
  sorry

variable [ConnectedSpace (Spec (CommRingCat.of k))]
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
variable (P : Compactification.Of (Spec (CommRingCat.of k)) X)
variable [Etale (Compactification.Of.ι P)]

variable [HasWeakSheafify P.obj.right.left.smallEtaleTopology
    (ModuleCat.{u + 1} Λ)]
variable [HasWeakSheafify
    (FieldExtension.baseChange k (AlgebraicClosure k)
      P.obj.right.hom).smallEtaleTopology
    (ModuleCat.{u + 1} Λ)]
variable [∀ G : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
    (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension G]
variable [∀ G : P.obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
    (smallEtalePullback
        (FieldExtension.toSource k (AlgebraicClosure k)
          P.obj.right.hom)).op.HasLeftKanExtension G]

/-- Global sections on the geometric compactification of the extension by zero
of the sheaf associated to a finite arithmetic fundamental-group module. -/
def geometricHc0Module : ModuleCat.{u + 1} Λ :=
  (((smallEtalePullback
        (FieldExtension.toSource k (AlgebraicClosure k) P.obj.right.hom)).sheafPullback
      (ModuleCat.{u + 1} Λ) P.obj.right.left.smallEtaleTopology
      (FieldExtension.baseChange k (AlgebraicClosure k)
        P.obj.right.hom).smallEtaleTopology).obj
    ((etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u + 1} Λ)).obj
      (associatedSheaf Λ (arithmeticPoint X ηbar) M))).obj.obj
        (Opposite.op (globalEtale
          (FieldExtension.baseChange k (AlgebraicClosure k) P.obj.right.hom)))

/-- Compactly supported geometric `H^2` of `F_ρ`, as a residual Galois module. -/
abbrev geometricHc2GaloisModule : Action AddCommGrpCat.{u + 1} Gal(AlgebraicClosure k/k) :=
  cohomologyCompactSupportGaloisModule X P
    ((sheafCompose X.left.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        (associatedSheaf Λ (arithmeticPoint X ηbar) M)) 2

omit [Etale (Compactification.Of.ι P)]
  [ConnectedSpace (geometricBaseChange X)]
  [HasWeakSheafify (geometricBaseChange X).smallEtaleTopology (ModuleCat.{u + 1} Λ)]
  [∀ G : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
    (smallEtalePullback (geometricToArithmeticHom X)).op.HasLeftKanExtension G]
  [ConnectedSpace (Spec (CommRingCat.of k))]
  [CompactSpace X.left] [QuasiSeparatedSpace X.left]
  [HasWeakSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
  [HasWeakSheafify
    (FieldExtension.baseChange k (AlgebraicClosure k) P.obj.right.hom).smallEtaleTopology
    (ModuleCat.{u + 1} Λ)]
  [∀ G : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
    (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension G]
  [∀ G : P.obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
    (smallEtalePullback
      (FieldExtension.toSource k (AlgebraicClosure k) P.obj.right.hom)).op.HasLeftKanExtension G] in
/-- Unfolding of compactly supported geometric `H^2` of `F_ρ`. -/
theorem geometricHc2GaloisModule_eq :
    geometricHc2GaloisModule X ηbar M P =
      cohomologyCompactSupportGaloisModule X P
        ((sheafCompose X.left.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
            (associatedSheaf Λ (arithmeticPoint X ηbar) M)) 2 :=
  rfl

/-- Tate twist of geometric coinvariants, forgotten to an abelian Galois module. -/
abbrev geometricCoinvariantsTate (hΛ : IsUnit (Nat.card Λ : k)) :
    Action AddCommGrpCat.{u + 1} Gal(AlgebraicClosure k/k) :=
  ((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).mapAction
      Gal(AlgebraicClosure k/k)).obj
    (tateTwist hΛ (geometricCoinvariants X ηbar M.obj))

omit [ConnectedSpace X.left]
  [HasWeakSheafify X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
  [∀ U : X.left.Etale,
    HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
  [HasWeakSheafify (geometricBaseChange X).smallEtaleTopology (ModuleCat.{u + 1} Λ)]
  [∀ G : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
    (smallEtalePullback (geometricToArithmeticHom X)).op.HasLeftKanExtension G]
  [X.left.smallEtaleTopology.HasSheafCompose
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})] in
/-- Unfolding of the forgotten Tate twist of geometric coinvariants. -/
theorem geometricCoinvariantsTate_eq (hΛ : IsUnit (Nat.card Λ : k)) :
    geometricCoinvariantsTate X ηbar M hΛ =
      ((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).mapAction
          Gal(AlgebraicClosure k/k)).obj
        (tateTwist hΛ (geometricCoinvariants X ηbar M.obj)) :=
  rfl

/-- The `Λ`-linear map on geometric coinvariants induced by a morphism of
representations, by descent of the geometric restriction of `f`. -/
def geometricCoinvariantsLinearMap
    {N : (finiteTypeDiscreteModule Λ
        (Aut (GeometricPoint.finiteFiber (arithmeticPoint X ηbar)))).FullSubcategory}
    (f : M ⟶ N) :
    geometricCoinvariantsModule X ηbar M.obj →ₗ[Λ]
      geometricCoinvariantsModule X ηbar N.obj :=
  let Mgeo := (geometricRestriction X ηbar M.obj).obj
  let fgeo := ((discreteModuleRes (geometricToArithmetic X ηbar).hom).map f.hom).hom
  @MonoidAlgebra.Coinvariants.lift Λ (Aut (GeometricPoint.finiteFiber ηbar))
    Mgeo.V _ _ _ (moduleOfAction Mgeo) _
    (geometricCoinvariantsModule X ηbar N.obj) _ _
    ((geometricCoinvariants_mk X ηbar N.obj).comp fgeo.hom.hom) fun _ _ ↦ sorry

/-- The map on Tate-twisted geometric coinvariants induced by a morphism of
representations, as residual Galois modules. -/
def geometricCoinvariantsTateMap (hΛ : IsUnit (Nat.card Λ : k))
    {N : (finiteTypeDiscreteModule Λ
        (Aut (GeometricPoint.finiteFiber (arithmeticPoint X ηbar)))).FullSubcategory}
    (f : M ⟶ N) :
    geometricCoinvariantsTate X ηbar M hΛ ⟶ geometricCoinvariantsTate X ηbar N hΛ where
  hom :=
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map
      (ModuleCat.ofHom (geometricCoinvariantsLinearMap X ηbar M f))
  comm := sorry

omit [ConnectedSpace X.left]
  [HasWeakSheafify X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
  [∀ U : X.left.Etale,
    HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
  [HasWeakSheafify (geometricBaseChange X).smallEtaleTopology (ModuleCat.{u + 1} Λ)]
  [∀ G : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
    (smallEtalePullback (geometricToArithmeticHom X)).op.HasLeftKanExtension G]
  [X.left.smallEtaleTopology.HasSheafCompose
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})] in
/-- The underlying abelian map of `geometricCoinvariantsTateMap` is the forgetful
image of `geometricCoinvariantsLinearMap`. -/
theorem geometricCoinvariantsTateMap_hom (hΛ : IsUnit (Nat.card Λ : k))
    {N : (finiteTypeDiscreteModule Λ
        (Aut (GeometricPoint.finiteFiber (arithmeticPoint X ηbar)))).FullSubcategory}
    (f : M ⟶ N) :
    (geometricCoinvariantsTateMap X ηbar M hΛ f).hom =
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map
        (ModuleCat.ofHom (geometricCoinvariantsLinearMap X ηbar M f)) :=
  rfl

/-- The map on compactly supported geometric `H^2` induced by a morphism of
representations. -/
def geometricHc2Map
    {N : (finiteTypeDiscreteModule Λ
        (Aut (GeometricPoint.finiteFiber (arithmeticPoint X ηbar)))).FullSubcategory}
    (f : M ⟶ N) :
    geometricHc2GaloisModule X ηbar M P ⟶ geometricHc2GaloisModule X ηbar N P where
  hom :=
    etaleCohomologyMap₁
      ((etaleAbelianSheafPullback₁
          (FieldExtension.toSource k (AlgebraicClosure k)
            P.obj.right.hom)).map
        ((etaleExtensionByZero (Compactification.Of.ι P) AddCommGrpCat.{u + 1}).map
          ((sheafCompose X.left.smallEtaleTopology
              (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map
            ((associatedSheafFunctor Λ (arithmeticPoint X ηbar)).map f))))
      2
  comm := sorry

omit [ConnectedSpace (geometricBaseChange X)]
  [HasWeakSheafify (geometricBaseChange X).smallEtaleTopology (ModuleCat.{u + 1} Λ)]
  [∀ G : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
    (smallEtalePullback (geometricToArithmeticHom X)).op.HasLeftKanExtension G]
  [ConnectedSpace (Spec (CommRingCat.of k))]
  [CompactSpace X.left] [QuasiSeparatedSpace X.left]
  [HasWeakSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
  [HasWeakSheafify
    (FieldExtension.baseChange k (AlgebraicClosure k) P.obj.right.hom).smallEtaleTopology
    (ModuleCat.{u + 1} Λ)]
  [∀ G : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
    (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension G]
  [∀ G : P.obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
    (smallEtalePullback
      (FieldExtension.toSource k (AlgebraicClosure k) P.obj.right.hom)).op.HasLeftKanExtension G] in
/-- The underlying abelian map of `geometricHc2Map` is cohomology of the extension by
zero of the associated sheaf morphism. -/
theorem geometricHc2Map_hom
    {N : (finiteTypeDiscreteModule Λ
        (Aut (GeometricPoint.finiteFiber (arithmeticPoint X ηbar)))).FullSubcategory}
    (f : M ⟶ N) :
    (geometricHc2Map X ηbar M P f).hom =
      etaleCohomologyMap₁
        ((etaleAbelianSheafPullback₁
            (FieldExtension.toSource k (AlgebraicClosure k)
              P.obj.right.hom)).map
          ((etaleExtensionByZero (Compactification.Of.ι P) AddCommGrpCat.{u + 1}).map
            ((sheafCompose X.left.smallEtaleTopology
                (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map
              ((associatedSheafFunctor Λ (arithmeticPoint X ηbar)).map f))))
        2 :=
  rfl

omit [HasWeakSheafify (geometricBaseChange X).smallEtaleTopology (ModuleCat.{u + 1} Λ)]
  [∀ G : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
    (smallEtalePullback (geometricToArithmeticHom X)).op.HasLeftKanExtension G]
  [HasWeakSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
  [HasWeakSheafify
    (FieldExtension.baseChange k (AlgebraicClosure k) P.obj.right.hom).smallEtaleTopology
    (ModuleCat.{u + 1} Λ)]
  [∀ G : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
    (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension G]
  [∀ G : P.obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
    (smallEtalePullback
      (FieldExtension.toSource k (AlgebraicClosure k) P.obj.right.hom)).op.HasLeftKanExtension G] in
include hCurve hSmooth hConnected in
/-- On a smooth geometrically connected projective curve, degree-two compactly
supported geometric cohomology is naturally isomorphic to inverse-cyclotomic-twisted
geometric coinvariants as an absolute Galois module. -/
theorem geometricHc2_iso_coinvariantsTate_natural [Projective X.hom]
    (hΛ : IsUnit (Nat.card Λ : k)) :
    ∃ i : ∀ M : (finiteTypeDiscreteModule Λ
        (Aut (GeometricPoint.finiteFiber (arithmeticPoint X ηbar)))).FullSubcategory,
        geometricHc2GaloisModule X ηbar M P ≅ geometricCoinvariantsTate X ηbar M hΛ,
      ∀ (M N : (finiteTypeDiscreteModule Λ
        (Aut (GeometricPoint.finiteFiber (arithmeticPoint X ηbar)))).FullSubcategory) (f : M ⟶ N),
        (i M).hom ≫ geometricCoinvariantsTateMap X ηbar M hΛ f =
          geometricHc2Map X ηbar M P f ≫ (i N).hom :=
  sorry

omit [HasWeakSheafify (geometricBaseChange X).smallEtaleTopology (ModuleCat.{u + 1} Λ)]
  [∀ G : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
    (smallEtalePullback (geometricToArithmeticHom X)).op.HasLeftKanExtension G]
  [X.left.smallEtaleTopology.HasSheafCompose
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})] in
include hCurve hSmooth hConnected in
/-- Compactly supported geometric global sections of a finite locally constant sheaf
on a smooth geometrically connected nonprojective curve vanish. -/
theorem geometricHc0_isZero_of_not_projective
    (h_not_proj : ¬ Projective X.hom) :
    IsZero (geometricHc0Module X ηbar M P) :=
  sorry

end AlgebraicGeometry.SchemeOverField
