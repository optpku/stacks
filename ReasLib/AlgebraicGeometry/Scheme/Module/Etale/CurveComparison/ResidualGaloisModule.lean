/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.Cyclotomic
public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.GeometricArithmetic
public import ReasLib.AlgebraicGeometry.Scheme.FundamentalGroup.GaloisComparison
public import ReasLib.AlgebraicGeometry.Scheme.GeometricPoint.FiniteEtale.FieldComparison
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LocallyConstantPullback
public import ReasLib.CategoryTheory.Action.ModuleCat.OpenStabilizer.Definition
public import ReasLib.RepresentationTheory.Coinvariants

/-!
# Residual Galois action on geometric coinvariants

Arithmetic lifts use the geometric-arithmetic exact sequence and the prescribed
algebraic-closure fibre comparison.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Action.ModuleCat
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
open AlgebraicGeometry.Scheme.Etale AlgebraicGeometry.Scheme.GeometricPoint
open scoped MonoidAlgebra

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale
open CategoryTheory.Action.ModuleCat

variable {k : Type u} [Field k]
variable {Λ : Type (u + 1)} [Ring Λ]
variable (X : SchemeOverField k)
variable [ConnectedSpace X.left] [ConnectedSpace (geometricBaseChange X)]
variable [ConnectedSpace (Spec (CommRingCat.of k))]
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]

/-- Restriction of a discrete arithmetic π₁-module along `geometricToArithmetic`. -/
def geometricRestriction (xbar : GeometricPoint (geometricBaseChange X))
    (Mρ : DiscreteModuleCat Λ (Aut (GeometricPoint.finiteFiber (arithmeticPoint X xbar)))) :
    DiscreteModuleCat Λ (Aut (GeometricPoint.finiteFiber xbar)) :=
  (discreteModuleRes (geometricToArithmetic X xbar).hom).obj Mρ

/-- The underlying Λ-module of geometric coinvariants of `Mρ`. -/
abbrev geometricCoinvariantsModule (xbar : GeometricPoint (geometricBaseChange X))
    (Mρ : DiscreteModuleCat Λ (Aut (GeometricPoint.finiteFiber (arithmeticPoint X xbar)))) :
    Type (u + 1) :=
  let Mgeo := (geometricRestriction X xbar Mρ).obj
  @MonoidAlgebra.Coinvariants Λ (Aut (GeometricPoint.finiteFiber xbar)) Mgeo.V _ _ _
    (moduleOfAction Mgeo) _

/-- The quotient map from `Mρ` to its geometric coinvariants. -/
def geometricCoinvariants_mk (xbar : GeometricPoint (geometricBaseChange X))
    (Mρ : DiscreteModuleCat Λ (Aut (GeometricPoint.finiteFiber (arithmeticPoint X xbar)))) :
    ((geometricRestriction X xbar Mρ).obj.V →ₗ[Λ]
      geometricCoinvariantsModule X xbar Mρ) :=
  let Mgeo := (geometricRestriction X xbar Mρ).obj
  @MonoidAlgebra.Coinvariants.mk Λ (Aut (GeometricPoint.finiteFiber xbar)) Mgeo.V _ _ _
    (moduleOfAction Mgeo) _

/-- The morphism `Spec(xbar.K) ⟶ Spec k̄` induced by the structure map of `X_{k̄}`. -/
def geometricPointToSpecClosure (xbar : GeometricPoint (geometricBaseChange X)) :
    Spec (CommRingCat.of xbar.K) ⟶ Spec (CommRingCat.of (AlgebraicClosure k)) :=
  xbar.hom ≫ FieldExtension.toBase k (AlgebraicClosure k) X.hom

/-- Forward comparison of finite étale fibers at `Spec k̄` and at the Galois point of `X`. -/
def specFiberToGaloisFiber (xbar : GeometricPoint (geometricBaseChange X))
    (Y : FiniteEtale (Spec (CommRingCat.of k))) :
    ((GeometricPoint.finiteFiber (specFieldGeometricPoint k (AlgebraicClosure k))).obj Y) →
      ((GeometricPoint.finiteFiber (galoisPoint X (arithmeticPoint X xbar))).obj Y) :=
  fun y ↦ Over.homMk (geometricPointToSpecClosure X xbar ≫ y.left) (w := sorry)

/-- The fiber comparison is bijective. -/
theorem specFiberToGaloisFiber_bijective (xbar : GeometricPoint (geometricBaseChange X))
    (Y : FiniteEtale (Spec (CommRingCat.of k))) :
    Function.Bijective (specFiberToGaloisFiber X xbar Y) :=
  sorry

/-- Descend a finite étale fibre point through affine coordinates along the
specified map from the geometric point to `Spec k̄`. -/
def specFiberInverse (xbar : GeometricPoint (geometricBaseChange X))
    (Y : FiniteEtale (Spec (CommRingCat.of k)))
    (y : ((GeometricPoint.finiteFiber (galoisPoint X (arithmeticPoint X xbar))).obj Y)) :
    ((GeometricPoint.finiteFiber (specFieldGeometricPoint k (AlgebraicClosure k))).obj Y) := by
  let φ : AlgebraicClosure k →+* xbar.K :=
    (Spec.preimage (geometricPointToSpecClosure X xbar)).hom
  letI : Algebra k xbar.K := (φ.comp (algebraMap k (AlgebraicClosure k))).toAlgebra
  letI : IsAlgClosed xbar.K := xbar.isAlgClosed
  let ι : AlgebraicClosure k →ₐ[k] xbar.K :=
    { toRingHom := φ
      commutes' := fun _ ↦ rfl }
  exact GeometricPoint.FieldComparison.inverse ι Y
    (Over.homMk y.left (w := sorry))

/-- The finite-fibre equivalence retains its fixed forward map and descends the
inverse through the affine coordinates along that same prescribed embedding. -/
def specFiberEquiv (xbar : GeometricPoint (geometricBaseChange X))
    (Y : FiniteEtale (Spec (CommRingCat.of k))) :
    ((GeometricPoint.finiteFiber (specFieldGeometricPoint k (AlgebraicClosure k))).obj Y) ≃
      ((GeometricPoint.finiteFiber (galoisPoint X (arithmeticPoint X xbar))).obj Y) :=
  { toFun := specFiberToGaloisFiber X xbar Y
    invFun := specFiberInverse X xbar Y
    left_inv := sorry
    right_inv := sorry }

@[simp]
theorem specFiberEquiv_apply (xbar : GeometricPoint (geometricBaseChange X))
    (Y : FiniteEtale (Spec (CommRingCat.of k)))
    (y : ((GeometricPoint.finiteFiber (specFieldGeometricPoint k (AlgebraicClosure k))).obj Y)) :
    specFiberEquiv X xbar Y y = specFiberToGaloisFiber X xbar Y y := rfl

@[simp]
theorem specFiberEquiv_symm_apply (xbar : GeometricPoint (geometricBaseChange X))
    (Y : FiniteEtale (Spec (CommRingCat.of k)))
    (y : ((GeometricPoint.finiteFiber (galoisPoint X (arithmeticPoint X xbar))).obj Y)) :
    (specFiberEquiv X xbar Y).symm y = specFiberInverse X xbar Y y := rfl

/-- Isomorphism of standard fiber functors at the two geometric points of `Spec k`. -/
def specFiberFunctorIso (xbar : GeometricPoint (geometricBaseChange X)) :
    GeometricPoint.finiteFiber (specFieldGeometricPoint k (AlgebraicClosure k)) ≅
      GeometricPoint.finiteFiber (galoisPoint X (arithmeticPoint X xbar)) :=
  NatIso.ofComponents
    (fun Y ↦
      { hom := FintypeCat.homMk (specFiberEquiv X xbar Y)
        inv := FintypeCat.homMk (specFiberEquiv X xbar Y).symm
        hom_inv_id := sorry
        inv_hom_id := sorry })
    fun _ ↦ sorry

/-- Canonical homomorphism `Gal(k̄/k) → π₁(Spec k, galoisPoint)` obtained by transporting
`galoisAlgClosureToFundamentalGroup` along the fiber comparison. -/
def galoisToGaloisPoint (xbar : GeometricPoint (geometricBaseChange X)) :
    Gal(AlgebraicClosure k/k) →*
      Aut (GeometricPoint.finiteFiber (galoisPoint X (arithmeticPoint X xbar))) :=
  (GeometricPoint.autHom (specFiberFunctorIso X xbar)).toMonoidHom.comp
    (galoisAlgClosureToFundamentalGroup k (AlgebraicClosure k))

/-- The Galois comparison at the specified field-spectrum point uses coordinate
reconstruction and the given fibre isomorphism in both directions. -/
def galoisPointEquiv (xbar : GeometricPoint (geometricBaseChange X)) :
    Gal(AlgebraicClosure k/k) ≃*
      Aut (GeometricPoint.finiteFiber (galoisPoint X (arithmeticPoint X xbar))) :=
  (galoisAlgClosureEquivFundamentalGroup k).trans (specFiberFunctorIso X xbar).conjAut

/-- The equivalence retains the original specified Galois action. -/
@[simp]
theorem galoisPointEquiv_apply (xbar : GeometricPoint (geometricBaseChange X))
    (σ : Gal(AlgebraicClosure k/k)) :
    galoisPointEquiv X xbar σ = galoisToGaloisPoint X xbar σ := rfl

/-- The inverse first transports back to the algebraic-closure fibre and then
reconstructs the field automorphism from its finite-level coordinates. -/
@[simp]
theorem galoisPointEquiv_symm_apply (xbar : GeometricPoint (geometricBaseChange X))
    (τ : Aut (GeometricPoint.finiteFiber (galoisPoint X (arithmeticPoint X xbar)))) :
    (galoisPointEquiv X xbar).symm τ =
      GaloisComparison.inverse ((specFiberFunctorIso X xbar).conjAut.symm τ) := rfl

/-- A lift of a Galois element to `π₁(X)` along `arithmeticToGalois`. -/
def arithmeticLift (xbar : GeometricPoint (geometricBaseChange X))
    (σ : Gal(AlgebraicClosure k/k)) :
    Aut (GeometricPoint.finiteFiber (arithmeticPoint X xbar)) :=
  Function.surjInv (arithmeticToGalois_surjective X (arithmeticPoint X xbar))
    (galoisToGaloisPoint X xbar σ)

/-- Residual Gal(k̄/k)-action on geometric coinvariants, descended from the arithmetic
π₁-action along the exact sequence of Lemma 58.14.3. -/
def geometricCoinvariants (xbar : GeometricPoint (geometricBaseChange X))
    (Mρ : DiscreteModuleCat Λ (Aut (GeometricPoint.finiteFiber (arithmeticPoint X xbar)))) :
    Action (ModuleCat.{u + 1} Λ) Gal(AlgebraicClosure k/k) :=
  let Mgeo := (geometricRestriction X xbar Mρ).obj
  -- Local instance justification (search instability): Aut-universes prevent global synthesis of `moduleOfAction` at this residual-action construction.
  letI := moduleOfAction Mgeo
  { V := ModuleCat.of Λ (geometricCoinvariantsModule X xbar Mρ)
    ρ :=
      { toFun := fun σ ↦
          ModuleCat.ofHom
            (MonoidAlgebra.Coinvariants.lift Λ (Aut (GeometricPoint.finiteFiber xbar)) Mgeo.V
              ((geometricCoinvariants_mk X xbar Mρ).comp (Mρ.obj.ρ (arithmeticLift X xbar σ)).hom)
              fun _ _ ↦ sorry)
        map_one' := sorry
        map_mul' := sorry } }

/-- The underlying module of geometric coinvariants is the named coinvariants quotient. -/
theorem geometricCoinvariants_V (xbar : GeometricPoint (geometricBaseChange X))
    (Mρ : DiscreteModuleCat Λ (Aut (GeometricPoint.finiteFiber (arithmeticPoint X xbar)))) :
    (geometricCoinvariants X xbar Mρ).V =
      ModuleCat.of Λ (geometricCoinvariantsModule X xbar Mρ) :=
  rfl

/-- Residual action of a Galois element on geometric coinvariants is descent of the
arithmetic π₁-action of any lift. -/
theorem geometricCoinvariants_residual (xbar : GeometricPoint (geometricBaseChange X))
    (Mρ : DiscreteModuleCat Λ (Aut (GeometricPoint.finiteFiber (arithmeticPoint X xbar))))
    (σ : Gal(AlgebraicClosure k/k)) (p : (geometricRestriction X xbar Mρ).obj.V) :
    ((geometricCoinvariants X xbar Mρ).ρ σ).hom
        (geometricCoinvariants_mk X xbar Mρ p) =
      geometricCoinvariants_mk X xbar Mρ ((Mρ.obj.ρ (arithmeticLift X xbar σ)).hom p) :=
  sorry

end AlgebraicGeometry.SchemeOverField
