/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Action.Basic
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Action.Limits
public import Mathlib.LinearAlgebra.Quotient.Basic
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import ReasLib.CategoryTheory.Action.ModuleCat.OpenStabilizer.Definition
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalLeftDerived
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Cochain
public import stacks_project.Chap59.Definition_59_57_2
public import stacks_project.Chap59.Remark_59_65_3
public import stacks_project.Chap64.Proposition_64_10_2_Trace
public import stacks_project.Chap64.Proposition_64_29_3_TateTwist
public import stacks_project.Chap64.Remark_64_30_1_Extension

/-!
# Derived G-coinvariants and conjugacy traces

This leaf owns underived G-coinvariants, the total left-derived functor
`LH_0(G, M) = M ⊗^L_{Λ[G]} Λ` in `D(Λ)`, the Frobenius endomorphism, and
conjugacy-class traces in `Λ♮`.
-/

@[expose] public section

open AlgebraicGeometry.Scheme
open CategoryTheory CategoryTheory.Action CategoryTheory.Action.ModuleCat
open CategoryTheory.Limits
open HomotopyCategory
open scoped Ring

universe u v

namespace ProfiniteGrp

variable (S : DegreeExtension.{u})

/-- Restriction of a continuous `Γ`-module along `inl : G → Γ`, as an ordinary linear action. -/
noncomputable def restrictAction {Λ : Type u} [Ring Λ]
    (M : DiscreteModuleCat Λ S.middle) :
    Action (ModuleCat.{u} Λ) S.G :=
  (Action.res (ModuleCat.{u} Λ) S.inl.toMonoidHom).obj M.obj

/-- Restriction of a continuous `Γ`-module along `inl : G → Γ`, as a discrete continuous
`G`-module. -/
noncomputable def restrictDiscrete {Λ : Type u} [Ring Λ]
    (M : DiscreteModuleCat Λ S.middle) :
    DiscreteModuleCat Λ S.G :=
  (discreteModuleRes S.inl).obj M

/-- The kernel of G-coinvariants of a linear G-action. -/
def coinvariantsKer {Λ : Type u} [Ring Λ] {G : Type u} [Group G]
    (M : Action (ModuleCat.{u} Λ) G) : Submodule Λ M.V :=
  Submodule.span Λ
    (Set.range fun gp : G × M.V ↦ (ModuleCat.Hom.hom (M.ρ gp.1)) gp.2 - gp.2)

/-- Underived G-coinvariants as a functor on linear G-actions. -/
noncomputable def actionCoinvariantsFunctor (Λ : Type u) [Ring Λ] (G : Type u) [Group G] :
    Action (ModuleCat.{u} Λ) G ⥤ ModuleCat.{u} Λ where
  obj M := ModuleCat.of Λ (M.V ⧸ coinvariantsKer M)
  map {M N} f :=
    ModuleCat.ofHom
      (Submodule.mapQ (coinvariantsKer M) (coinvariantsKer N)
        (ModuleCat.Hom.hom f.hom) sorry)
  map_id := sorry
  map_comp := sorry

/-- The coinvariants functor is additive. -/
instance actionCoinvariantsFunctor_additive (Λ : Type u) [Ring Λ] (G : Type u) [Group G] :
    (actionCoinvariantsFunctor Λ G).Additive :=
  sorry

/-- The standard derived-category model on linear `G`-actions. -/
noncomputable instance instHasDerivedCategory_actionModuleCat
    (Λ : Type u) [Ring Λ] (G : Type u) [Group G] :
    HasDerivedCategory (Action (ModuleCat.{u} Λ) G) :=
  HasDerivedCategory.standard _

/-- Underived G-coinvariants of a continuous `Γ`-module. -/
noncomputable def underivedCoinvariants {Λ : Type u} [Ring Λ]
    (M : DiscreteModuleCat Λ S.middle) : ModuleCat.{u} Λ :=
  (actionCoinvariantsFunctor Λ S.G).obj (restrictAction S M)

/-- The total left-derived coinvariants functor `LG = - ⊗^L_{Λ[G]} Λ`. -/
noncomputable def derivedCoinvariantsFunctor (Λ : Type u) [Ring Λ]
    [(Functor.Homotopy.toDerived (actionCoinvariantsFunctor Λ S.G)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (Action (ModuleCat.{u} Λ) S.G) (ComplexShape.up ℤ))] :
    DerivedCategory (Action (ModuleCat.{u} Λ) S.G) ⥤ DerivedCategory (ModuleCat.{u} Λ) :=
  Functor.LeftDerived.Homotopy.functor (actionCoinvariantsFunctor Λ S.G)

/-- Derived G-coinvariants `LH_0(G, M) = M ⊗^L_{Λ[G]} Λ` in `D(Λ)`. -/
noncomputable def derivedCoinvariants {Λ : Type u} [Ring Λ]
    [(Functor.Homotopy.toDerived (actionCoinvariantsFunctor Λ S.G)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (Action (ModuleCat.{u} Λ) S.G) (ComplexShape.up ℤ))]
    (M : DiscreteModuleCat Λ S.middle) :
    DerivedCategory (ModuleCat.{u} Λ) :=
  (derivedCoinvariantsFunctor S Λ).obj
    (((DerivedCategory.singleFunctors (Action (ModuleCat.{u} Λ) S.G)).functor (0 : ℤ)).obj
      (restrictAction S M))

/-- Derived G-coinvariants of an already restricted discrete `G`-module. -/
noncomputable def derivedCoinvariantsOnG {Λ : Type u} [Ring Λ]
    [(Functor.Homotopy.toDerived (actionCoinvariantsFunctor Λ S.G)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (Action (ModuleCat.{u} Λ) S.G) (ComplexShape.up ℤ))]
    (N : DiscreteModuleCat Λ S.G) :
    DerivedCategory (ModuleCat.{u} Λ) :=
  (derivedCoinvariantsFunctor S Λ).obj
    (((DerivedCategory.singleFunctors (Action (ModuleCat.{u} Λ) S.G)).functor (0 : ℤ)).obj N.obj)

/-- Unfolding of derived coinvariants as the total left-derived functor of coinvariants
applied to `Res_G M` placed in degree `0`. -/
theorem derivedCoinvariants_eq {Λ : Type u} [Ring Λ]
    [(Functor.Homotopy.toDerived (actionCoinvariantsFunctor Λ S.G)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (Action (ModuleCat.{u} Λ) S.G) (ComplexShape.up ℤ))]
    (M : DiscreteModuleCat Λ S.middle) :
    derivedCoinvariants S M =
      (derivedCoinvariantsFunctor S Λ).obj
        (((DerivedCategory.singleFunctors (Action (ModuleCat.{u} Λ) S.G)).functor (0 : ℤ)).obj
          (restrictAction S M)) :=
  sorry

/-- The `Λ`-linear action of a group element on a continuous module. -/
noncomputable def smulEnd {Λ : Type v} [Ring Λ] {G : Type u} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (M : DiscreteModuleCat Λ G) (γ : G) : Module.End Λ M.obj.V :=
  ModuleCat.Hom.hom (M.obj.ρ γ)

/-- The endomorphism of the restricted `G`-module induced by a lift `γ ∈ Γ`. -/
noncomputable def frobeniusRestrictIso {Λ : Type u} [Ring Λ]
    (M : DiscreteModuleCat Λ S.middle) (γ : S.middle) :
    restrictAction S M ≅ restrictAction S M where
  hom := { hom := M.obj.ρ γ, comm := fun _ => sorry }
  inv := { hom := M.obj.ρ (γ⁻¹), comm := fun _ => sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The Frobenius endomorphism of derived G-coinvariants induced by a degree-one lift. -/
noncomputable def frobeniusEndWith {Λ : Type u} [Ring Λ]
    [(Functor.Homotopy.toDerived (actionCoinvariantsFunctor Λ S.G)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (Action (ModuleCat.{u} Λ) S.G) (ComplexShape.up ℤ))]
    (M : DiscreteModuleCat Λ S.middle) (γ : S.middle) :
    CategoryTheory.End (derivedCoinvariants S M) :=
  (derivedCoinvariantsFunctor S Λ).map
    (((DerivedCategory.singleFunctors (Action (ModuleCat.{u} Λ) S.G)).functor (0 : ℤ)).map
      (frobeniusRestrictIso S M γ).hom)

/-- The Frobenius endomorphism of derived G-coinvariants, using a chosen degree-one lift. -/
noncomputable def frobeniusEnd {Λ : Type u} [Ring Λ]
    [(Functor.Homotopy.toDerived (actionCoinvariantsFunctor Λ S.G)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (Action (ModuleCat.{u} Λ) S.G) (ComplexShape.up ℤ))]
    (M : DiscreteModuleCat Λ S.middle) :
    CategoryTheory.End (derivedCoinvariants S M) :=
  frobeniusEndWith S M S.degreeOneLift

/-- The conjugacy class of the `n`-th power of a representative of `c`. -/
noncomputable def powClass {G : Type u} [Group G] (c : ConjClasses G) (n : ℕ) :
    ConjClasses G :=
  ConjClasses.mk (Quotient.out c ^ n)

/-- The finite-projective trace of a conjugacy class acting on `M`. -/
noncomputable def conjClassTrace {Λ : Type v} [Ring Λ]
    (M : DiscreteModuleCat Λ S.middle)
    [Module.Finite Λ M.obj.V] [Module.Projective Λ M.obj.V]
    (c : ConjClasses S.middle) : Λ♮ :=
  LinearMap.FiniteProjective.traceNatural (smulEnd M (Quotient.out c))

/-- The class trace on a representative is the finite-projective trace of that element. -/
theorem conjClassTrace_mk {Λ : Type v} [Ring Λ]
    (M : DiscreteModuleCat Λ S.middle)
    [Module.Finite Λ M.obj.V] [Module.Projective Λ M.obj.V] (γ : S.middle) :
    conjClassTrace S M (ConjClasses.mk γ) =
      LinearMap.FiniteProjective.traceNatural (smulEnd M γ) :=
  sorry

/-- Finite `ℓ`-cohomological dimension of a topological group: continuous cohomology of
discrete `ℓ`-torsion `ℤ`-modules vanishes in large degree. -/
def HasFiniteEllCohomologicalDimension (ℓ : ℕ) (G : Type u)
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] : Prop :=
  ∃ d : ℕ, ∀ (M : DiscreteModuleCat ℤ G) (i : ℕ),
    (∀ x : M.obj.V, ℓ • x = 0) →
      d < i → IsZero (DiscreteModuleCat.continuousCohomology G M i)

/-- Finite projective derived coinvariants, using finite `ℓ`-cd for `ℓ` not dividing `q`
and invertibility of `q` in `Λ`. -/
theorem isPerfect_derivedCoinvariants {Λ : Type u} [Ring Λ] [Finite Λ]
    [(Functor.Homotopy.toDerived (actionCoinvariantsFunctor Λ S.G)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (Action (ModuleCat.{u} Λ) S.G) (ComplexShape.up ℤ))]
    (M : DiscreteModuleCat Λ S.middle)
    [Module.Finite Λ M.obj.V] [Module.Projective Λ M.obj.V]
    {q : ℕ} (hunit : IsUnit (q : Λ))
    (hcd : ∀ ℓ : ℕ, ¬ ℓ ∣ q → HasFiniteEllCohomologicalDimension ℓ S.G) :
    DerivedCategory.IsPerfect (derivedCoinvariants S M) :=
  sorry

/-- The trace `Tr(F^n | LH_0(G, M))` in `Λ♮`. -/
noncomputable def traceFrobeniusPow {Λ : Type u} [Ring Λ]
    [(Functor.Homotopy.toDerived (actionCoinvariantsFunctor Λ S.G)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (Action (ModuleCat.{u} Λ) S.G) (ComplexShape.up ℤ))]
    (M : DiscreteModuleCat Λ S.middle)
    [Module.Finite Λ M.obj.V] [Module.Projective Λ M.obj.V]
    (hperf : DerivedCategory.IsPerfect (derivedCoinvariants S M)) (n : ℕ) : Λ♮ :=
  hperf.traceNatural (frobeniusEnd S M ^ n)

/-- The trace `Tr(F^n | LH_0(G, M))` is independent of the chosen degree-one lift. -/
theorem traceFrobeniusPow_independent {Λ : Type u} [Ring Λ]
    [(Functor.Homotopy.toDerived (actionCoinvariantsFunctor Λ S.G)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (Action (ModuleCat.{u} Λ) S.G) (ComplexShape.up ℤ))]
    (M : DiscreteModuleCat Λ S.middle)
    [Module.Finite Λ M.obj.V] [Module.Projective Λ M.obj.V]
    (hperf : DerivedCategory.IsPerfect (derivedCoinvariants S M))
    (γ γ' : S.middle) (hγ : S.deg γ = hatZOne.{u}) (hγ' : S.deg γ' = hatZOne.{u})
    (n : ℕ) :
    hperf.traceNatural (frobeniusEndWith S M γ ^ n) =
      hperf.traceNatural (frobeniusEndWith S M γ' ^ n) :=
  sorry

/-- G-invariants of a linear G-action. -/
def actionInvariants {Λ : Type u} [Ring Λ] {G : Type u} [Group G]
    (M : Action (ModuleCat.{u} Λ) G) : Submodule Λ M.V where
  carrier := { m | ∀ g : G, ModuleCat.Hom.hom (M.ρ g) m = m }
  zero_mem' := sorry
  add_mem' := sorry
  smul_mem' := sorry

/-- Underived G-invariants as a functor on linear G-actions. -/
noncomputable def actionInvariantsFunctor (Λ : Type u) [Ring Λ] (G : Type u) [Group G] :
    Action (ModuleCat.{u} Λ) G ⥤ ModuleCat.{u} Λ where
  obj M := ModuleCat.of Λ (actionInvariants M)
  map {M N} f :=
    ModuleCat.ofHom
      { toFun := fun m => ⟨(ModuleCat.Hom.hom f.hom) m.val, sorry⟩
        map_add' := sorry
        map_smul' := sorry }
  map_id := sorry
  map_comp := sorry

/-- The invariants functor is additive. -/
instance actionInvariantsFunctor_additive (Λ : Type u) [Ring Λ] (G : Type u) [Group G] :
    (actionInvariantsFunctor Λ G).Additive :=
  sorry

/-- The total right-derived invariants functor `RG = RH^0(G, -)`. -/
noncomputable def derivedInvariantsFunctor (Λ : Type u) [Ring Λ]
    [Functor.HasRightDerivedFunctor
      (Functor.RightDerived.Cochain.toDerived (actionInvariantsFunctor Λ S.G))
      (HomologicalComplex.quasiIso (Action (ModuleCat.{u} Λ) S.G) (ComplexShape.up ℤ))] :
    DerivedCategory (Action (ModuleCat.{u} Λ) S.G) ⥤ DerivedCategory (ModuleCat.{u} Λ) :=
  Functor.RightDerived.Cochain.functor (actionInvariantsFunctor Λ S.G)

/-- Derived G-invariants `RH^0(G, M)` in `D(Λ)`. -/
noncomputable def derivedInvariants {Λ : Type u} [Ring Λ]
    [Functor.HasRightDerivedFunctor
      (Functor.RightDerived.Cochain.toDerived (actionInvariantsFunctor Λ S.G))
      (HomologicalComplex.quasiIso (Action (ModuleCat.{u} Λ) S.G) (ComplexShape.up ℤ))]
    (M : DiscreteModuleCat Λ S.middle) :
    DerivedCategory (ModuleCat.{u} Λ) :=
  (derivedInvariantsFunctor S Λ).obj
    (((DerivedCategory.singleFunctors (Action (ModuleCat.{u} Λ) S.G)).functor (0 : ℤ)).obj
      (restrictAction S M))

/-- The Frobenius endomorphism of derived G-invariants induced by a lift `γ ∈ Γ`. -/
noncomputable def frobeniusEndInvariantsWith {Λ : Type u} [Ring Λ]
    [Functor.HasRightDerivedFunctor
      (Functor.RightDerived.Cochain.toDerived (actionInvariantsFunctor Λ S.G))
      (HomologicalComplex.quasiIso (Action (ModuleCat.{u} Λ) S.G) (ComplexShape.up ℤ))]
    (M : DiscreteModuleCat Λ S.middle) (γ : S.middle) :
    CategoryTheory.End (derivedInvariants S M) :=
  (derivedInvariantsFunctor S Λ).map
    (((DerivedCategory.singleFunctors (Action (ModuleCat.{u} Λ) S.G)).functor (0 : ℤ)).map
      (frobeniusRestrictIso S M γ).hom)

/-- The Frobenius endomorphism of derived G-invariants, using a chosen degree-one lift. -/
noncomputable def frobeniusEndInvariants {Λ : Type u} [Ring Λ]
    [Functor.HasRightDerivedFunctor
      (Functor.RightDerived.Cochain.toDerived (actionInvariantsFunctor Λ S.G))
      (HomologicalComplex.quasiIso (Action (ModuleCat.{u} Λ) S.G) (ComplexShape.up ℤ))]
    (M : DiscreteModuleCat Λ S.middle) :
    CategoryTheory.End (derivedInvariants S M) :=
  frobeniusEndInvariantsWith S M S.degreeOneLift

/-- Unfolding of `frobeniusEndInvariants` as the action of the chosen degree-one lift. -/
theorem frobeniusEndInvariants_spec {Λ : Type u} [Ring Λ]
    [Functor.HasRightDerivedFunctor
      (Functor.RightDerived.Cochain.toDerived (actionInvariantsFunctor Λ S.G))
      (HomologicalComplex.quasiIso (Action (ModuleCat.{u} Λ) S.G) (ComplexShape.up ℤ))]
    (M : DiscreteModuleCat Λ S.middle) :
    frobeniusEndInvariants S M = frobeniusEndInvariantsWith S M S.degreeOneLift :=
  sorry

/-- Continuous group cohomology `H^i(G, M)` of a restricted `Γ`-module. -/
noncomputable def continuousCohomologyModule {Λ : Type u} [Ring Λ]
    [Functor.HasRightDerivedFunctor
      (Functor.RightDerived.Cochain.toDerived (actionInvariantsFunctor Λ S.G))
      (HomologicalComplex.quasiIso (Action (ModuleCat.{u} Λ) S.G) (ComplexShape.up ℤ))]
    (M : DiscreteModuleCat Λ S.middle) (i : ℕ) : ModuleCat.{u} Λ :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} Λ) (i : ℤ)).obj (derivedInvariants S M)

/-- The Tate twist `M(-1)` of a discrete continuous `G`-module along a modular character. -/
noncomputable def tateTwistRestrict {Λ : Type u} [CommRing Λ] {n : ℕ} [NeZero n]
    (χ : S.G →* (ZMod n)ˣ) (M : DiscreteModuleCat Λ S.middle) :
    DiscreteModuleCat Λ S.G :=
  tateTwist χ (restrictDiscrete S M)

end ProfiniteGrp
