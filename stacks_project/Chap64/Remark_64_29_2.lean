module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.RepresentationTheory.Invariants
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve
public import stacks_project.Chap58.Lemma_58_14_3_Induced
public import stacks_project.Chap64.Lemma_64_29_1
public import stacks_project.Chap64.Remark_64_29_2_Cohomology
import Mathlib.Tactic.CrossRefAttribute

/-!
# Functorial identifications of geometric cohomology of locally constant sheaves

Remark 64.29.2 records the identifications of geometric `H^0` with geometric
`π₁`-invariants and of compactly supported geometric `H^2` with Tate-twisted
coinvariants, when `X` is projective, together with vanishing of compactly
supported `H^0` when `X` is not projective.
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
variable [Curve X] [Smooth X.hom] [GeometricallyConnected X.hom]
variable [ConnectedSpace X.left] [ConnectedSpace (geometricBaseChange X)]
variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
variable (ηbar : GeometricPoint (geometricBaseChange X))
variable [HasWeakSheafify X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
variable [∀ U : X.left.Etale,
    HasWeakSheafify ((X.left.smallEtaleTopology).over U) (ModuleCat.{u + 1} Λ)]
variable [HasWeakSheafify (geometricBaseChange X).smallEtaleTopology (ModuleCat.{u + 1} Λ)]
variable [∀ P : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
    (smallEtalePullback (geometricToArithmeticHom X)).op.HasLeftKanExtension P]
variable [HasSheafify (geometricBaseChange X).smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [HasExt (Sheaf (geometricBaseChange X).smallEtaleTopology AddCommGrpCat.{u + 1})]
variable [(geometricBaseChange X).smallEtaleTopology.HasSheafCompose
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})]
variable [(X.left.smallEtaleTopology).HasSheafCompose
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})]
variable (M : (finiteTypeDiscreteModule Λ
    (Aut (standardFiniteEtaleFiber (arithmeticPoint X ηbar)))).FullSubcategory)

/-- Geometric `π₁(X_k̄, η̄)`-invariants of `M`, as a `Λ`-module. -/
abbrev geometricPi1Invariants : ModuleCat.{u + 1} Λ :=
  (Rep.invariantsFunctor Λ (Aut (standardFiniteEtaleFiber ηbar))).obj
    ((Rep.ActionToRep Λ (Aut (standardFiniteEtaleFiber ηbar))).obj
      (geometricRestriction X ηbar M.obj).obj)

/-- Unfolding of geometric `π₁`-invariants as `Rep.invariantsFunctor` of the geometric
restriction. -/
theorem geometricPi1Invariants_eq :
    geometricPi1Invariants X ηbar M =
      (Rep.invariantsFunctor Λ (Aut (standardFiniteEtaleFiber ηbar))).obj
        ((Rep.ActionToRep Λ (Aut (standardFiniteEtaleFiber ηbar))).obj
          (geometricRestriction X ηbar M.obj).obj) :=
  rfl

/-- The sheaf morphism `F_ρ ⟶ F_ρ'` associated with a morphism of finite discrete
`π₁`-modules. -/
def discreteModuleSheafMap
    {N : (finiteTypeDiscreteModule Λ
        (Aut (standardFiniteEtaleFiber (arithmeticPoint X ηbar)))).FullSubcategory}
    (f : M ⟶ N) :
    sheafOfDiscreteModule Λ (arithmeticPoint X ηbar) M ⟶
      sheafOfDiscreteModule Λ (arithmeticPoint X ηbar) N :=
  ((finiteTypeLocallyConstantModule_equivalence_finitePi1LambdaModules Λ
      (arithmeticPoint X ηbar)).inverse.map f).hom

/-- Unfolding of the sheaf morphism associated with a morphism of representations. -/
theorem discreteModuleSheafMap_eq
    {N : (finiteTypeDiscreteModule Λ
        (Aut (standardFiniteEtaleFiber (arithmeticPoint X ηbar)))).FullSubcategory}
    (f : M ⟶ N) :
    discreteModuleSheafMap X ηbar M f =
      ((finiteTypeLocallyConstantModule_equivalence_finitePi1LambdaModules Λ
          (arithmeticPoint X ηbar)).inverse.map f).hom :=
  rfl

/-- The map on geometric `π₁`-invariants induced by a morphism of representations. -/
def geometricPi1InvariantsMap
    {N : (finiteTypeDiscreteModule Λ
        (Aut (standardFiniteEtaleFiber (arithmeticPoint X ηbar)))).FullSubcategory}
    (f : M ⟶ N) :
    geometricPi1Invariants X ηbar M ⟶ geometricPi1Invariants X ηbar N :=
  (Rep.invariantsFunctor Λ (Aut (standardFiniteEtaleFiber ηbar))).map
    ((Rep.ActionToRep Λ (Aut (standardFiniteEtaleFiber ηbar))).map
      ((discreteModuleRes (geometricToArithmetic X ηbar).hom).map f.hom).hom)

/-- Unfolding of the induced map on geometric `π₁`-invariants. -/
theorem geometricPi1InvariantsMap_eq
    {N : (finiteTypeDiscreteModule Λ
        (Aut (standardFiniteEtaleFiber (arithmeticPoint X ηbar)))).FullSubcategory}
    (f : M ⟶ N) :
    geometricPi1InvariantsMap X ηbar M f =
      (Rep.invariantsFunctor Λ (Aut (standardFiniteEtaleFiber ηbar))).map
        ((Rep.ActionToRep Λ (Aut (standardFiniteEtaleFiber ηbar))).map
          ((discreteModuleRes (geometricToArithmetic X ηbar).hom).map f.hom).hom) :=
  rfl

/-- Remark 64.29.2 (1): if `X` is projective, then `H^0(X_k̄, F_ρ)` is identified
with the geometric `π₁(X_k̄, η̄)`-invariants of `M`, functorially in `ρ`. -/
@[stacks 03VL]
theorem geometricH0_iso_pi1Invariants [Projective X.hom] :
    IsIsomorphic
      (geometricModuleEtaleHq X (sheafOfDiscreteModule Λ (arithmeticPoint X ηbar) M) 0)
      (geometricPi1Invariants X ηbar M) :=
  sorry

/-- Naturality of the geometric `H^0` identification in morphisms of representations. -/
theorem geometricH0_iso_pi1Invariants_natural [Projective X.hom]
    {N : (finiteTypeDiscreteModule Λ
        (Aut (standardFiniteEtaleFiber (arithmeticPoint X ηbar)))).FullSubcategory}
    (f : M ⟶ N) :
    ∃ (iM : geometricModuleEtaleHq X
              (sheafOfDiscreteModule Λ (arithmeticPoint X ηbar) M) 0 ≅
            geometricPi1Invariants X ηbar M)
      (iN : geometricModuleEtaleHq X
              (sheafOfDiscreteModule Λ (arithmeticPoint X ηbar) N) 0 ≅
            geometricPi1Invariants X ηbar N),
      iM.hom ≫ geometricPi1InvariantsMap X ηbar M f =
        geometricModuleEtaleHqMap X (discreteModuleSheafMap X ηbar M f) 0 ≫ iN.hom :=
  sorry

variable [ConnectedSpace (Spec (CommRingCat.of k))]
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
variable (P : Compactification.Of (Spec (CommRingCat.of k)) X)
variable [Etale (Compactification.Of.ι P)]

/-- The ambient compactification of `X`, as a scheme over `Spec k`. -/
abbrev compactificationOver : SchemeOverField k :=
  P.obj.right

/-- Unfolding of the ambient compactification of `X`. -/
theorem compactificationOver_eq :
    compactificationOver X P = P.obj.right :=
  rfl

variable [HasWeakSheafify (compactificationOver X P).left.smallEtaleTopology
    (ModuleCat.{u + 1} Λ)]
variable [HasWeakSheafify
    (FieldExtension.baseChange k (AlgebraicClosure k)
      (compactificationOver X P).hom).smallEtaleTopology
    (ModuleCat.{u + 1} Λ)]
variable [∀ G : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
    (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension G]
variable [∀ G : (compactificationOver X P).left.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
    (smallEtalePullback
        (FieldExtension.toSource k (AlgebraicClosure k)
          (compactificationOver X P).hom)).op.HasLeftKanExtension G]
variable [HasSheafify
    (FieldExtension.baseChange k (AlgebraicClosure k)
      (compactificationOver X P).hom).smallEtaleTopology
    AddCommGrpCat.{u + 1}]
variable [HasExt
    (Sheaf
      (FieldExtension.baseChange k (AlgebraicClosure k)
        (compactificationOver X P).hom).smallEtaleTopology
      AddCommGrpCat.{u + 1})]
variable [(FieldExtension.baseChange k (AlgebraicClosure k)
      (compactificationOver X P).hom).smallEtaleTopology.HasSheafCompose
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})]

/-- Compactly supported geometric `H^2` of `F_ρ`, as a residual Galois module. -/
abbrev geometricHc2GaloisModule : Action AddCommGrpCat.{u + 1} Gal(AlgebraicClosure k/k) :=
  cohomologyCompactSupportGaloisModule X P
    (abelianSheafOfModuleSheaf Λ (sheafOfDiscreteModule Λ (arithmeticPoint X ηbar) M)) 2

/-- Unfolding of compactly supported geometric `H^2` of `F_ρ`. -/
theorem geometricHc2GaloisModule_eq :
    geometricHc2GaloisModule X ηbar M P =
      cohomologyCompactSupportGaloisModule X P
        (abelianSheafOfModuleSheaf Λ
          (sheafOfDiscreteModule Λ (arithmeticPoint X ηbar) M)) 2 :=
  rfl

/-- Tate twist of geometric coinvariants, forgotten to an abelian Galois module. -/
abbrev geometricCoinvariantsTate (hΛ : IsUnit (Nat.card Λ : k)) :
    Action AddCommGrpCat.{u + 1} Gal(AlgebraicClosure k/k) :=
  ((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).mapAction
      Gal(AlgebraicClosure k/k)).obj
    (tateTwist hΛ (geometricCoinvariants X ηbar M.obj))

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
        (Aut (standardFiniteEtaleFiber (arithmeticPoint X ηbar)))).FullSubcategory}
    (f : M ⟶ N) :
    geometricCoinvariantsModule X ηbar M.obj →ₗ[Λ]
      geometricCoinvariantsModule X ηbar N.obj :=
  let Mgeo := (geometricRestriction X ηbar M.obj).obj
  let fgeo := ((discreteModuleRes (geometricToArithmetic X ηbar).hom).map f.hom).hom
  @MonoidAlgebra.Coinvariants.lift Λ (Aut (standardFiniteEtaleFiber ηbar))
    Mgeo.V _ _ _ (moduleOfAction Mgeo) _
    (geometricCoinvariantsModule X ηbar N.obj) _ _
    ((geometricCoinvariants_mk X ηbar N.obj).comp fgeo.hom.hom) fun _ _ ↦ sorry

/-- The map on Tate-twisted geometric coinvariants induced by a morphism of
representations, as residual Galois modules. -/
def geometricCoinvariantsTateMap (hΛ : IsUnit (Nat.card Λ : k))
    {N : (finiteTypeDiscreteModule Λ
        (Aut (standardFiniteEtaleFiber (arithmeticPoint X ηbar)))).FullSubcategory}
    (f : M ⟶ N) :
    geometricCoinvariantsTate X ηbar M hΛ ⟶ geometricCoinvariantsTate X ηbar N hΛ where
  hom :=
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map
      (ModuleCat.ofHom (geometricCoinvariantsLinearMap X ηbar M f))
  comm := sorry

/-- The underlying abelian map of `geometricCoinvariantsTateMap` is the forgetful
image of `geometricCoinvariantsLinearMap`. -/
theorem geometricCoinvariantsTateMap_hom (hΛ : IsUnit (Nat.card Λ : k))
    {N : (finiteTypeDiscreteModule Λ
        (Aut (standardFiniteEtaleFiber (arithmeticPoint X ηbar)))).FullSubcategory}
    (f : M ⟶ N) :
    (geometricCoinvariantsTateMap X ηbar M hΛ f).hom =
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map
        (ModuleCat.ofHom (geometricCoinvariantsLinearMap X ηbar M f)) :=
  rfl

/-- The map on compactly supported geometric `H^2` induced by a morphism of
representations. -/
def geometricHc2Map
    {N : (finiteTypeDiscreteModule Λ
        (Aut (standardFiniteEtaleFiber (arithmeticPoint X ηbar)))).FullSubcategory}
    (f : M ⟶ N) :
    geometricHc2GaloisModule X ηbar M P ⟶ geometricHc2GaloisModule X ηbar N P where
  hom :=
    etaleCohomologyMap₁
      ((etaleAbelianSheafPullback₁
          (FieldExtension.toSource k (AlgebraicClosure k)
            (compactificationOver X P).hom)).map
        ((etaleExtensionByZero (Compactification.Of.ι P) AddCommGrpCat.{u + 1}).map
          ((sheafCompose X.left.smallEtaleTopology
              (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map
            (discreteModuleSheafMap X ηbar M f))))
      2
  comm := sorry

/-- The underlying abelian map of `geometricHc2Map` is cohomology of the extension by
zero of the associated sheaf morphism. -/
theorem geometricHc2Map_hom
    {N : (finiteTypeDiscreteModule Λ
        (Aut (standardFiniteEtaleFiber (arithmeticPoint X ηbar)))).FullSubcategory}
    (f : M ⟶ N) :
    (geometricHc2Map X ηbar M P f).hom =
      etaleCohomologyMap₁
        ((etaleAbelianSheafPullback₁
            (FieldExtension.toSource k (AlgebraicClosure k)
              (compactificationOver X P).hom)).map
          ((etaleExtensionByZero (Compactification.Of.ι P) AddCommGrpCat.{u + 1}).map
            ((sheafCompose X.left.smallEtaleTopology
                (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map
              (discreteModuleSheafMap X ηbar M f))))
        2 :=
  rfl

/-- Remark 64.29.2 (2): if `X` is projective, then `H_c^2(X_k̄, F_ρ)` is identified
with the Tate twist of the geometric `π₁(X_k̄, η̄)`-coinvariants of `M`, as
`Gal(AlgebraicClosure k/k)`-modules, functorially in `ρ`. -/
@[stacks 03VL]
theorem geometricHc2_iso_coinvariantsTate_of_projective [Projective X.hom]
    (hΛ : IsUnit (Nat.card Λ : k)) :
    IsIsomorphic (geometricHc2GaloisModule X ηbar M P)
      (geometricCoinvariantsTate X ηbar M hΛ) :=
  sorry

/-- Naturality of the compactly supported `H^2` identification in morphisms of
representations. -/
theorem geometricHc2_iso_coinvariantsTate_natural [Projective X.hom]
    {N : (finiteTypeDiscreteModule Λ
        (Aut (standardFiniteEtaleFiber (arithmeticPoint X ηbar)))).FullSubcategory}
    (f : M ⟶ N) (hΛ : IsUnit (Nat.card Λ : k)) :
    ∃ (iM : geometricHc2GaloisModule X ηbar M P ≅
            geometricCoinvariantsTate X ηbar M hΛ)
      (iN : geometricHc2GaloisModule X ηbar N P ≅
            geometricCoinvariantsTate X ηbar N hΛ),
      iM.hom ≫ geometricCoinvariantsTateMap X ηbar M hΛ f =
        geometricHc2Map X ηbar M P f ≫ iN.hom :=
  sorry

/-- Remark 64.29.2 (3): if `X` is not projective, then
`H_c^0(X_k̄, F_ρ) = 0`. -/
@[stacks 03VL]
theorem geometricHc0_isZero_of_not_projective
    (h_not_proj : ¬ Projective X.hom) :
    IsZero
      (geometricModuleEtaleHqCompactSupport X P
        (sheafOfDiscreteModule Λ (arithmeticPoint X ηbar) M) 0) :=
  sorry

end AlgebraicGeometry.SchemeOverField
