/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.MonoidAlgebra.Lift
public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
public import ReasLib.CategoryTheory.Action.ModuleCat.OpenStabilizer.Definition
public import stacks_project.Chap58.Lemma_58_5_5_Fiber
public import stacks_project.Chap58.Lemma_58_14_3_Induced
public import stacks_project.Chap58.Remark_58_6_4_GaloisAction
public import stacks_project.Chap58.Theorem_58_6_2_InducedHom
public import stacks_project.Chap59.Remark_59_65_3
public import stacks_project.Chap64.Lemma_64_15_9_Coinvariants

/-!
# Geometric coinvariants and cyclotomic Tate twists

This leaf owns coinvariants of a discrete π₁-module under the geometric fundamental
group, the residual Gal(k̄/k)-action, and the finite-level cyclotomic Tate twist.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Action.ModuleCat
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
open AlgebraicGeometry.Scheme.Etale AlgebraicGeometry.Scheme.GeometricPoint
open scoped MonoidAlgebra

noncomputable section

universe u v w

namespace AlgebraicGeometry.Scheme.Etale

variable {Λ : Type (u + 1)} [Ring Λ] [Finite Λ]

/-- A finite ring has nonzero cardinality. -/
theorem natCard_ne_zero_of_finite_ring : NeZero (Nat.card Λ) :=
  ⟨by
    have : Nonempty Λ := ⟨0⟩
    exact Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩⟩

/-- Finite rings have nonzero cardinality, as a typeclass instance. -/
instance instNeZero_natCard : NeZero (Nat.card Λ) :=
  natCard_ne_zero_of_finite_ring

/-- In a finite ring, the cardinality annihilates the additive group. -/
theorem finite_ring_cast_card_eq_zero : (Nat.card Λ : Λ) = 0 :=
  sorry

/-- The unique ring homomorphism `ZMod (Nat.card Λ) →+* Λ` induced by `n • 1 = 0`. -/
def zmodCardRingHom : ZMod (Nat.card Λ) →+* Λ :=
  (Ideal.Quotient.lift (Ideal.span {(Nat.card Λ : ℤ)}) (Int.castRingHom Λ)
      sorry).comp
    (Int.quotientSpanNatEquivZMod (Nat.card Λ)).symm.toRingHom

/-- The group homomorphism sending a Galois element to its underlying ring automorphism. -/
def galoisToRingAut (k : Type u) [Field k] :
    Gal(AlgebraicClosure k/k) →* (AlgebraicClosure k ≃+* AlgebraicClosure k) where
  toFun σ := σ.toRingEquiv
  map_one' := rfl
  map_mul' := sorry

/-- Invertibility of `Nat.card Λ` in `k` implies that `k̄` contains exactly `n` nth roots of unity. -/
theorem rootsOfUnity_card_eq (k : Type u) [Field k]
    (hΛ : IsUnit (Nat.card Λ : k)) :
    Nat.card { x // x ∈ rootsOfUnity (Nat.card Λ) (AlgebraicClosure k) } =
      Nat.card Λ :=
  sorry

/-- The finite-level cyclotomic character valued in `Λˣ`, obtained by composing
`modularCyclotomicCharacter` with the unique map from `ZMod n` into the finite ring `Λ`. -/
def cyclotomicCharacterMod (k : Type u) [Field k]
    (hΛ : IsUnit (Nat.card Λ : k)) :
    Gal(AlgebraicClosure k/k) →* Λˣ :=
  (Units.map (zmodCardRingHom (Λ := Λ)).toMonoidHom).comp <|
    (modularCyclotomicCharacter (AlgebraicClosure k)
        (rootsOfUnity_card_eq (Λ := Λ) k hΛ)).comp
      (galoisToRingAut k)

/-- Evaluating the finite-level cyclotomic character recovers the image of the modular
cyclotomic character in `Λ`. -/
theorem cyclotomicCharacterMod_apply (k : Type u) [Field k]
    (hΛ : IsUnit (Nat.card Λ : k)) (σ : Gal(AlgebraicClosure k/k)) :
    (cyclotomicCharacterMod (Λ := Λ) k hΛ σ : Λ) =
      zmodCardRingHom
        (modularCyclotomicCharacter (AlgebraicClosure k)
            (rootsOfUnity_card_eq (Λ := Λ) k hΛ)
          (galoisToRingAut k σ)) :=
  sorry

variable {G : Type v} [Group G]

/-- Scalar multiplications as additive endomorphisms of the underlying module. -/
def scalarToAddEnd (M : Action (ModuleCat.{max (u + 1) v} Λ) G) : Λ →+* AddMonoid.End M.V where
  toFun r := DistribSMul.toAddMonoidHom M.V r
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

/-- The additive endomorphism underlying a linear `G`-action. -/
def actionToAddEnd (M : Action (ModuleCat.{max (u + 1) v} Λ) G) : G →* AddMonoid.End M.V where
  toFun g := (M.ρ g).hom.toAddMonoidHom
  map_one' := sorry
  map_mul' := sorry

/-- The monoid-algebra representation on additive endomorphisms associated to a linear action. -/
def actionToMonoidAlgebraAddEnd (M : Action (ModuleCat.{max (u + 1) v} Λ) G) :
    Λ[G] →+* AddMonoid.End M.V :=
  MonoidAlgebra.liftNCRingHom (scalarToAddEnd M) (actionToAddEnd M) fun _ _ ↦ sorry

/-- The left `Λ[G]`-module structure on the underlying module of a linear `G`-action. -/
instance moduleOfAction (M : Action (ModuleCat.{max (u + 1) v} Λ) G) : Module (Λ[G]) M.V :=
  Module.compHom M.V (actionToMonoidAlgebraAddEnd M)

/-- Left multiplication by a unit of `Λ` as a `Λ`-linear endomorphism. -/
def unitsSMulEnd {P : Type w} [AddCommGroup P] [Module Λ P] (u : Λˣ) :
    Module.End Λ P where
  toFun p := (u : Λ) • p
  map_add' := fun x y ↦ smul_add (u : Λ) x y
  map_smul' := fun r p ↦ sorry

/-- Tate twist of a linear Gal(k̄/k)-action: `σ` acts by `χ(σ)⁻¹ • ρ(σ)`. -/
def tateTwist {k : Type u} [Field k] (hΛ : IsUnit (Nat.card Λ : k))
    (M : Action (ModuleCat.{u + 1} Λ) Gal(AlgebraicClosure k/k)) :
    Action (ModuleCat.{u + 1} Λ) Gal(AlgebraicClosure k/k) where
  V := M.V
  ρ :=
    { toFun := fun σ ↦
        ModuleCat.ofHom
          ((unitsSMulEnd (cyclotomicCharacterMod (Λ := Λ) k hΛ σ)⁻¹).comp (M.ρ σ).hom)
      map_one' := sorry
      map_mul' := sorry }

/-- The underlying module of a Tate twist is unchanged. -/
theorem tateTwist_V {k : Type u} [Field k] (hΛ : IsUnit (Nat.card Λ : k))
    (M : Action (ModuleCat.{u + 1} Λ) Gal(AlgebraicClosure k/k)) :
    (tateTwist hΛ M).V = M.V :=
  rfl

/-- Evaluating the Tate-twisted action inserts the inverse cyclotomic scalar. -/
theorem tateTwist_ρ {k : Type u} [Field k] (hΛ : IsUnit (Nat.card Λ : k))
    (M : Action (ModuleCat.{u + 1} Λ) Gal(AlgebraicClosure k/k))
    (σ : Gal(AlgebraicClosure k/k)) :
    (tateTwist hΛ M).ρ σ =
      ModuleCat.ofHom
        ((unitsSMulEnd (cyclotomicCharacterMod (Λ := Λ) k hΛ σ)⁻¹).comp (M.ρ σ).hom) :=
  rfl

end AlgebraicGeometry.Scheme.Etale

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
    (Mρ : DiscreteModuleCat Λ (Aut (standardFiniteEtaleFiber (arithmeticPoint X xbar)))) :
    DiscreteModuleCat Λ (Aut (standardFiniteEtaleFiber xbar)) :=
  (discreteModuleRes (geometricToArithmetic X xbar).hom).obj Mρ

/-- The underlying Λ-module of geometric coinvariants of `Mρ`. -/
abbrev geometricCoinvariantsModule (xbar : GeometricPoint (geometricBaseChange X))
    (Mρ : DiscreteModuleCat Λ (Aut (standardFiniteEtaleFiber (arithmeticPoint X xbar)))) :
    Type (u + 1) :=
  let Mgeo := (geometricRestriction X xbar Mρ).obj
  @MonoidAlgebra.Coinvariants Λ (Aut (standardFiniteEtaleFiber xbar)) Mgeo.V _ _ _
    (moduleOfAction Mgeo) _

/-- The quotient map from `Mρ` to its geometric coinvariants. -/
def geometricCoinvariants_mk (xbar : GeometricPoint (geometricBaseChange X))
    (Mρ : DiscreteModuleCat Λ (Aut (standardFiniteEtaleFiber (arithmeticPoint X xbar)))) :
    ((geometricRestriction X xbar Mρ).obj.V →ₗ[Λ]
      geometricCoinvariantsModule X xbar Mρ) :=
  let Mgeo := (geometricRestriction X xbar Mρ).obj
  @MonoidAlgebra.Coinvariants.mk Λ (Aut (standardFiniteEtaleFiber xbar)) Mgeo.V _ _ _
    (moduleOfAction Mgeo) _

/-- The morphism `Spec(xbar.K) ⟶ Spec k̄` induced by the structure map of `X_{k̄}`. -/
def geometricPointToSpecClosure (xbar : GeometricPoint (geometricBaseChange X)) :
    Spec (CommRingCat.of xbar.K) ⟶ Spec (CommRingCat.of (AlgebraicClosure k)) :=
  xbar.hom ≫ FieldExtension.toBase k (AlgebraicClosure k) X.hom

/-- Forward comparison of finite étale fibers at `Spec k̄` and at the Galois point of `X`. -/
def specFiberToGaloisFiber (xbar : GeometricPoint (geometricBaseChange X))
    (Y : FiniteEtale (Spec (CommRingCat.of k))) :
    finiteEtaleFiberObj (specFieldGeometricPoint k (AlgebraicClosure k)) Y →
      finiteEtaleFiberObj (galoisPoint X (arithmeticPoint X xbar)) Y :=
  fun y ↦ Over.homMk (geometricPointToSpecClosure X xbar ≫ y.left) (w := sorry)

/-- The fiber comparison is bijective. -/
theorem specFiberToGaloisFiber_bijective (xbar : GeometricPoint (geometricBaseChange X))
    (Y : FiniteEtale (Spec (CommRingCat.of k))) :
    Function.Bijective (specFiberToGaloisFiber X xbar Y) :=
  sorry

/-- Equivalence of finite étale fibers at the canonical algebraic-closure point and at the
Galois point of `X`. -/
def specFiberEquiv (xbar : GeometricPoint (geometricBaseChange X))
    (Y : FiniteEtale (Spec (CommRingCat.of k))) :
    finiteEtaleFiberObj (specFieldGeometricPoint k (AlgebraicClosure k)) Y ≃
      finiteEtaleFiberObj (galoisPoint X (arithmeticPoint X xbar)) Y :=
  Equiv.ofBijective (specFiberToGaloisFiber X xbar Y)
    (specFiberToGaloisFiber_bijective X xbar Y)

/-- Isomorphism of standard fiber functors at the two geometric points of `Spec k`. -/
def specFiberFunctorIso (xbar : GeometricPoint (geometricBaseChange X)) :
    standardFiniteEtaleFiber (specFieldGeometricPoint k (AlgebraicClosure k)) ≅
      standardFiniteEtaleFiber (galoisPoint X (arithmeticPoint X xbar)) :=
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
      Aut (standardFiniteEtaleFiber (galoisPoint X (arithmeticPoint X xbar))) :=
  (inducedAutHom_of_fiberIso (specFiberFunctorIso X xbar)).toMonoidHom.comp
    (galoisAlgClosureToFundamentalGroup k (AlgebraicClosure k))

/-- A lift of a Galois element to `π₁(X)` along `arithmeticToGalois`. -/
def arithmeticLift (xbar : GeometricPoint (geometricBaseChange X))
    (σ : Gal(AlgebraicClosure k/k)) :
    Aut (standardFiniteEtaleFiber (arithmeticPoint X xbar)) :=
  Function.surjInv (arithmeticToGalois_surjective X (arithmeticPoint X xbar))
    (galoisToGaloisPoint X xbar σ)

/-- Residual Gal(k̄/k)-action on geometric coinvariants, descended from the arithmetic
π₁-action along the exact sequence of Lemma 58.14.3. -/
def geometricCoinvariants (xbar : GeometricPoint (geometricBaseChange X))
    (Mρ : DiscreteModuleCat Λ (Aut (standardFiniteEtaleFiber (arithmeticPoint X xbar)))) :
    Action (ModuleCat.{u + 1} Λ) Gal(AlgebraicClosure k/k) :=
  let Mgeo := (geometricRestriction X xbar Mρ).obj
  -- Local instance justification (search instability): Aut-universes prevent global synthesis of `moduleOfAction` at this residual-action construction.
  letI := moduleOfAction Mgeo
  { V := ModuleCat.of Λ (geometricCoinvariantsModule X xbar Mρ)
    ρ :=
      { toFun := fun σ ↦
          ModuleCat.ofHom
            (MonoidAlgebra.Coinvariants.lift Λ (Aut (standardFiniteEtaleFiber xbar)) Mgeo.V
              ((geometricCoinvariants_mk X xbar Mρ).comp (Mρ.obj.ρ (arithmeticLift X xbar σ)).hom)
              fun _ _ ↦ sorry)
        map_one' := sorry
        map_mul' := sorry } }

/-- The underlying module of geometric coinvariants is the named coinvariants quotient. -/
theorem geometricCoinvariants_V (xbar : GeometricPoint (geometricBaseChange X))
    (Mρ : DiscreteModuleCat Λ (Aut (standardFiniteEtaleFiber (arithmeticPoint X xbar)))) :
    (geometricCoinvariants X xbar Mρ).V =
      ModuleCat.of Λ (geometricCoinvariantsModule X xbar Mρ) :=
  rfl

/-- Residual action of a Galois element on geometric coinvariants is descent of the
arithmetic π₁-action of any lift. -/
theorem geometricCoinvariants_residual (xbar : GeometricPoint (geometricBaseChange X))
    (Mρ : DiscreteModuleCat Λ (Aut (standardFiniteEtaleFiber (arithmeticPoint X xbar))))
    (σ : Gal(AlgebraicClosure k/k)) (p : (geometricRestriction X xbar Mρ).obj.V) :
    ((geometricCoinvariants X xbar Mρ).ρ σ).hom
        (geometricCoinvariants_mk X xbar Mρ p) =
      geometricCoinvariants_mk X xbar Mρ ((Mρ.obj.ρ (arithmeticLift X xbar σ)).hom p) :=
  sorry

end AlgebraicGeometry.SchemeOverField

end
