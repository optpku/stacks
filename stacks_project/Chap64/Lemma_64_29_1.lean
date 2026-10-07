module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve
public import stacks_project.Chap64.Lemma_64_29_1_CompactSupport
public import stacks_project.Chap64.Lemma_64_29_1_GaloisModule
public import stacks_project.Chap64.Lemma_64_29_1_Sheaf

/-!
# Lemma 64.29.1

Canonical identification of compactly supported geometric étale cohomology in
degree two with Tate-twisted geometric coinvariants of a finite discrete π₁-module.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Action.ModuleCat
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale
open AlgebraicGeometry.SchemeOverField
open CategoryTheory.ObjectProperty
open scoped AlgebraicGeometry MonoidAlgebra

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]
variable {Λ : Type (u + 1)} [Ring Λ] [Finite Λ]
variable (X : SchemeOverField k)
variable [Curve X] [Smooth X.hom] [GeometricallyConnected X.hom]
variable [ConnectedSpace X.left] [ConnectedSpace (geometricBaseChange X)]
variable [ConnectedSpace (Spec (CommRingCat.of k))]
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
variable [HasWeakSheafify X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
variable [∀ U : X.left.Etale,
    HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
variable [X.left.smallEtaleTopology.HasSheafCompose
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})]
variable (xbar : GeometricPoint (geometricBaseChange X))
variable (Mρ : (finiteTypeDiscreteModule Λ
    (Aut (standardFiniteEtaleFiber (arithmeticPoint X xbar)))).FullSubcategory)
variable (P : Compactification.Of (Spec (CommRingCat.of k)) X)

/-- Inflation of geometric coinvariants to a discrete `π₁(X)`-module, with trivial geometric
fundamental-group action. -/
def inflationOfGeometricCoinvariants :
    (finiteTypeDiscreteModule Λ
      (Aut (standardFiniteEtaleFiber (arithmeticPoint X xbar)))).FullSubcategory :=
  let Mgeo := (geometricRestriction X xbar Mρ.obj).obj
  -- Local instance justification (search instability): Aut-universes prevent global synthesis of `moduleOfAction` at this residual-action construction.
  letI := moduleOfAction Mgeo
  ⟨⟨{ V := ModuleCat.of Λ (geometricCoinvariantsModule X xbar Mρ.obj)
      ρ :=
        { toFun := fun γ ↦
            ModuleCat.ofHom
              (MonoidAlgebra.Coinvariants.lift Λ (Aut (standardFiniteEtaleFiber xbar)) Mgeo.V
                ((geometricCoinvariants_mk X xbar Mρ.obj).comp (Mρ.obj.obj.ρ γ).hom)
                fun _ _ ↦ sorry)
          map_one' := sorry
          map_mul' := sorry } },
    sorry⟩,
  sorry⟩

/-- The canonical quotient map of discrete `π₁(X)`-modules from `Mρ` onto geometric
coinvariants, inflated with trivial geometric action. -/
def coinvariantsQuotientHom :
    Mρ.obj.obj ⟶ (inflationOfGeometricCoinvariants X xbar Mρ).obj.obj where
  hom := ModuleCat.ofHom (geometricCoinvariants_mk X xbar Mρ.obj)
  comm := fun _ ↦ sorry

/-- The sheaf morphism `F_ρ ⟶ F''` onto the maximal geometrically constant quotient,
associated to inflation of geometric coinvariants. -/
def geometricallyConstantQuotient :
    sheafOfDiscreteModule Λ (arithmeticPoint X xbar) Mρ ⟶
      sheafOfDiscreteModule Λ (arithmeticPoint X xbar)
        (inflationOfGeometricCoinvariants X xbar Mρ) :=
  ((finiteTypeLocallyConstantModule_equivalence_finitePi1LambdaModules Λ
      (arithmeticPoint X xbar)).inverse.map
    (homMk (homMk (coinvariantsQuotientHom X xbar Mρ)))).hom

/-- Compactly supported cohomology of the geometrically constant quotient, as a Galois module. -/
def cohomologyCompactSupportConstantQuotient :
    Action AddCommGrpCat.{u + 1} Gal(AlgebraicClosure k/k) :=
  cohomologyCompactSupportGaloisModule X P
    (abelianSheafOfModuleSheaf Λ
      (sheafOfDiscreteModule Λ (arithmeticPoint X xbar)
        (inflationOfGeometricCoinvariants X xbar Mρ)))
    2

/-- The comparison morphism on compactly supported cohomology induced by
`geometricallyConstantQuotient`. -/
def compactSupportToCoinvariants :
    cohomologyCompactSupportGaloisModule X P
        (abelianSheafOfModuleSheaf Λ
          (sheafOfDiscreteModule Λ (arithmeticPoint X xbar) Mρ)) 2 ⟶
      cohomologyCompactSupportConstantQuotient X xbar Mρ P where
  hom :=
    let Ybar := P.obj.right
    etaleCohomologyMap₁
      ((etaleAbelianSheafPullback₁
          (FieldExtension.toSource k (AlgebraicClosure k) Ybar.hom)).map
        ((etaleExtensionByZero (Compactification.Of.ι P) AddCommGrpCat.{u + 1}).map
          ((sheafCompose X.left.smallEtaleTopology
              (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map
            (geometricallyConstantQuotient X xbar Mρ))))
      2
  comm := fun _ ↦ sorry

/-- The comparison morphism intertwines the Galois action on compactly supported cohomology
with the residual action on the geometrically constant quotient. -/
theorem compactSupportToCoinvariants_equivariant
    (σ : Gal(AlgebraicClosure k/k)) :
    (cohomologyCompactSupportGaloisModule X P
          (abelianSheafOfModuleSheaf Λ
            (sheafOfDiscreteModule Λ (arithmeticPoint X xbar) Mρ)) 2).ρ σ ≫
        (compactSupportToCoinvariants X xbar Mρ P).hom =
      (compactSupportToCoinvariants X xbar Mρ P).hom ≫
        (cohomologyCompactSupportConstantQuotient X xbar Mρ P).ρ σ :=
  sorry

/-- Lemma 64.29.1. There is a canonical isomorphism
`H_c²(X_{k̄}, F_ρ) ≅ M_{π₁(X_{k̄}, η̄)}(-1)` of `Gal(k̄/k)`-modules, where the
subscript denotes coinvariants and `(-1)` is the cyclotomic Tate twist. -/
@[stacks 03VK]
theorem compactSupport_iso_geometricCoinvariantsTateTwist
    (hΛ : IsUnit (Nat.card Λ : k)) :
    IsIsomorphic
      (cohomologyCompactSupportGaloisModule X P
        (abelianSheafOfModuleSheaf Λ
          (sheafOfDiscreteModule Λ (arithmeticPoint X xbar) Mρ)) 2)
      (((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).mapAction
          Gal(AlgebraicClosure k/k)).obj
        (tateTwist hΛ (geometricCoinvariants X xbar Mρ.obj))) :=
  sorry

end AlgebraicGeometry.SchemeOverField

end
