/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.FiniteType
public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.RingHom.Finite
public import Mathlib.RingTheory.RingHom.Smooth

/-!
# Complete module dévissages

A complete dévissage is a finite nonempty chain of finite modules over changing
commutative algebras, equipped with finite-free comparison maps and the usual
finiteness, smoothness, fibre, cokernel, and terminal conditions.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Module.Devissage

/-- One stage in a complete dévissage over a prime `r` of `R`. -/
structure Stage (R : Type u) [CommRing R] (r : PrimeSpectrum R) where
  /-- The finite-module coefficient algebra at this stage. -/
  A : CommAlgCat.{u} R
  /-- The smooth intermediate algebra at this stage. -/
  B : CommAlgCat.{u} R
  /-- The finite `A`-module at this stage. -/
  M : FGModuleCat.{u} A
  /-- The map `B → A`. -/
  toA : B ⟶ A
  /-- The number of generators in the free source of `α`. -/
  rank : ℕ
  /-- The `B`-linear map from the finite free module to `M` restricted to `B`. -/
  α : ModuleCat.of B (Fin rank → B) ⟶
    (ModuleCat.restrictScalars toA.hom.toRingHom).obj M.obj
  /-- The prime of `B` lying over `r`. -/
  p : PrimeSpectrum B
  /-- The prime `p` is the extended ideal `rB`. -/
  prime_eq : p.asIdeal = Ideal.map (algebraMap R B) r.asIdeal

namespace Stage

/-- Build one dévissage stage from its algebras, module, map, rank, and chosen prime. -/
def of {R : Type u} [CommRing R] {r : PrimeSpectrum R}
    (A B : CommAlgCat.{u} R) (M : FGModuleCat.{u} A) (toA : B ⟶ A)
    (rank : ℕ)
    (α : ModuleCat.of B (Fin rank → B) ⟶
      (ModuleCat.restrictScalars toA.hom.toRingHom).obj M.obj)
    (p : PrimeSpectrum B)
    (prime_eq : p.asIdeal = Ideal.map (algebraMap R B) r.asIdeal) :
    Stage R r where
  A := A
  B := B
  M := M
  toA := toA
  rank := rank
  α := α
  p := p
  prime_eq := prime_eq

/-- The stage built by `of` has the specified free-module map. -/
theorem of_α {R : Type u} [CommRing R] {r : PrimeSpectrum R}
    (A B : CommAlgCat.{u} R) (M : FGModuleCat.{u} A) (toA : B ⟶ A)
    (rank : ℕ)
    (α : ModuleCat.of B (Fin rank → B) ⟶
      (ModuleCat.restrictScalars toA.hom.toRingHom).obj M.obj)
    (p : PrimeSpectrum B)
    (prime_eq : p.asIdeal = Ideal.map (algebraMap R B) r.asIdeal) :
    (Stage.of A B M toA rank α p prime_eq).α = α := sorry

/-- The residue-field base change of the free-module map in a dévissage stage. -/
def fiberMap {R : Type u} [CommRing R] {r : PrimeSpectrum R} (D : Stage R r) :
    (ModuleCat.extendScalars (algebraMap D.B D.p.asIdeal.ResidueField)).obj
        (ModuleCat.of D.B (Fin D.rank → D.B)) ⟶
      (ModuleCat.extendScalars (algebraMap D.B D.p.asIdeal.ResidueField)).obj
        ((ModuleCat.restrictScalars D.toA.hom.toRingHom).obj D.M.obj) :=
  (ModuleCat.extendScalars (algebraMap D.B D.p.asIdeal.ResidueField)).map D.α

/-- `fiberMap` is scalar extension of the stage map `α` to the residue field. -/
theorem fiberMap_def {R : Type u} [CommRing R] {r : PrimeSpectrum R} (D : Stage R r) :
    D.fiberMap =
      (ModuleCat.extendScalars (algebraMap D.B D.p.asIdeal.ResidueField)).map D.α := sorry

end Stage

/-- A finite, nonempty chain constituting a complete dévissage of `N/S/R` over `r`. -/
structure Complete (R : Type u) [CommRing R] (S : FGAlgCat.{u} R)
    (N : FGModuleCat.{u} S.obj) (r : PrimeSpectrum R) where
  /-- The final zero-based index of the nonempty chain. -/
  last : ℕ
  /-- The stages of the dévissage. -/
  stage : Fin (last + 1) → Stage R r
  /-- The initial `R`-algebra map `S → A₀`. -/
  initial : S.obj ⟶ (stage 0).A
  /-- The initial map is surjective. -/
  initial_surjective : Function.Surjective initial
  /-- The initial map is of finite presentation. -/
  initial_finitePresentation : initial.hom.toRingHom.FinitePresentation
  /-- The transition map `Bᵢ → Aᵢ₊₁`. -/
  transition (i : Fin last) : (stage i.castSucc).B ⟶ (stage i.succ).A
  /-- Every transition map is surjective. -/
  transition_surjective (i : Fin last) : Function.Surjective (transition i)
  /-- Every transition map is of finite presentation. -/
  transition_finitePresentation (i : Fin last) :
    (transition i).hom.toRingHom.FinitePresentation
  /-- Every map `Bᵢ → Aᵢ` is finite. -/
  finite_toA (i : Fin (last + 1)) : (stage i).toA.hom.toRingHom.Finite
  /-- Every structural map `R → Bᵢ` is smooth. -/
  smooth (i : Fin (last + 1)) : (algebraMap R (stage i).B).Smooth
  /-- Every affine structural map `Spec Bᵢ → Spec R` has geometrically irreducible fibres. -/
  geometricallyIrreducible (i : Fin (last + 1)) :
    AlgebraicGeometry.GeometricallyIrreducible
      (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (algebraMap R (stage i).B)))
  /-- The initial comparison `N ≅ M₀` as `S`-modules exists. -/
  initialIso : IsIsomorphic N.obj
    ((ModuleCat.restrictScalars initial.hom.toRingHom).obj (stage 0).M.obj)
  /-- The comparison between `cokernel(αᵢ)` and `Mᵢ₊₁` as `Bᵢ`-modules exists. -/
  transitionIso (i : Fin last) : IsIsomorphic (cokernel (stage i.castSucc).α)
    ((ModuleCat.restrictScalars (transition i).hom.toRingHom).obj (stage i.succ).M.obj)
  /-- Every residue-field base change of `αᵢ` is bijective. -/
  fiber_bijective (i : Fin (last + 1)) : Function.Bijective (stage i).fiberMap
  /-- The cokernel of the final map is zero. -/
  terminal_isZero : IsZero (cokernel (stage (Fin.last last)).α)

namespace Complete

/-- Assemble a complete dévissage from its concrete stages, maps, comparisons, and laws. -/
def ofStages {R : Type u} [CommRing R] {S : FGAlgCat.{u} R}
    {N : FGModuleCat.{u} S.obj} {r : PrimeSpectrum R}
    (last : ℕ) (stage : Fin (last + 1) → Stage R r)
    (initial : S.obj ⟶ (stage 0).A)
    (initial_surjective : Function.Surjective initial)
    (initial_finitePresentation : initial.hom.toRingHom.FinitePresentation)
    (transition : (i : Fin last) → (stage i.castSucc).B ⟶ (stage i.succ).A)
    (transition_surjective : ∀ i, Function.Surjective (transition i))
    (transition_finitePresentation : ∀ i,
      (transition i).hom.toRingHom.FinitePresentation)
    (finite_toA : ∀ i, (stage i).toA.hom.toRingHom.Finite)
    (smooth : ∀ i, (algebraMap R (stage i).B).Smooth)
    (geometricallyIrreducible : ∀ i,
      AlgebraicGeometry.GeometricallyIrreducible
        (AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (algebraMap R (stage i).B))))
    (initialIso : IsIsomorphic N.obj
      ((ModuleCat.restrictScalars initial.hom.toRingHom).obj (stage 0).M.obj))
    (transitionIso : ∀ i, IsIsomorphic (cokernel (stage i.castSucc).α)
      ((ModuleCat.restrictScalars (transition i).hom.toRingHom).obj (stage i.succ).M.obj))
    (fiber_bijective : ∀ i, Function.Bijective (stage i).fiberMap)
    (terminal_isZero : IsZero (cokernel (stage (Fin.last last)).α)) :
    Complete R S N r where
  last := last
  stage := stage
  initial := initial
  initial_surjective := initial_surjective
  initial_finitePresentation := initial_finitePresentation
  transition := transition
  transition_surjective := transition_surjective
  transition_finitePresentation := transition_finitePresentation
  finite_toA := finite_toA
  smooth := smooth
  geometricallyIrreducible := geometricallyIrreducible
  initialIso := initialIso
  transitionIso := transitionIso
  fiber_bijective := fiber_bijective
  terminal_isZero := terminal_isZero

/-- The complete dévissage built by `ofStages` has the specified family of stages. -/
theorem ofStages_stage {R : Type u} [CommRing R] {S : FGAlgCat.{u} R}
    {N : FGModuleCat.{u} S.obj} {r : PrimeSpectrum R}
    (last : ℕ) (stage : Fin (last + 1) → Stage R r)
    (initial : S.obj ⟶ (stage 0).A)
    (initial_surjective : Function.Surjective initial)
    (initial_finitePresentation : initial.hom.toRingHom.FinitePresentation)
    (transition : (i : Fin last) → (stage i.castSucc).B ⟶ (stage i.succ).A)
    (transition_surjective : ∀ i, Function.Surjective (transition i))
    (transition_finitePresentation : ∀ i,
      (transition i).hom.toRingHom.FinitePresentation)
    (finite_toA : ∀ i, (stage i).toA.hom.toRingHom.Finite)
    (smooth : ∀ i, (algebraMap R (stage i).B).Smooth)
    (geometricallyIrreducible : ∀ i,
      AlgebraicGeometry.GeometricallyIrreducible
        (AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (algebraMap R (stage i).B))))
    (initialIso : IsIsomorphic N.obj
      ((ModuleCat.restrictScalars initial.hom.toRingHom).obj (stage 0).M.obj))
    (transitionIso : ∀ i, IsIsomorphic (cokernel (stage i.castSucc).α)
      ((ModuleCat.restrictScalars (transition i).hom.toRingHom).obj (stage i.succ).M.obj))
    (fiber_bijective : ∀ i, Function.Bijective (stage i).fiberMap)
    (terminal_isZero : IsZero (cokernel (stage (Fin.last last)).α))
    (i : Fin (last + 1)) :
    (Complete.ofStages last stage initial initial_surjective initial_finitePresentation
      transition transition_surjective transition_finitePresentation finite_toA smooth
      geometricallyIrreducible initialIso transitionIso fiber_bijective terminal_isZero).stage i =
        stage i := sorry

/-- The initial map in a complete dévissage is surjective and finitely presented. -/
theorem initial_spec {R : Type u} [CommRing R] {S : FGAlgCat.{u} R}
    {N : FGModuleCat.{u} S.obj} {r : PrimeSpectrum R} (D : Complete R S N r) :
    Function.Surjective D.initial ∧ D.initial.hom.toRingHom.FinitePresentation := sorry

/-- Every transition map in a complete dévissage is surjective and finitely presented. -/
theorem transition_spec {R : Type u} [CommRing R] {S : FGAlgCat.{u} R}
    {N : FGModuleCat.{u} S.obj} {r : PrimeSpectrum R} (D : Complete R S N r)
    (i : Fin D.last) :
    Function.Surjective (D.transition i) ∧
      (D.transition i).hom.toRingHom.FinitePresentation := sorry

/-- At every stage, `R → Bᵢ` is smooth with geometrically irreducible fibres. -/
theorem baseMap_spec {R : Type u} [CommRing R] {S : FGAlgCat.{u} R}
    {N : FGModuleCat.{u} S.obj} {r : PrimeSpectrum R} (D : Complete R S N r)
    (i : Fin (D.last + 1)) :
    (algebraMap R (D.stage i).B).Smooth ∧
      AlgebraicGeometry.GeometricallyIrreducible
        (AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (algebraMap R (D.stage i).B))) := sorry

/-- At every stage, `pᵢ = rBᵢ` and the residue-field base change of `αᵢ` is bijective. -/
theorem fiber_spec {R : Type u} [CommRing R] {S : FGAlgCat.{u} R}
    {N : FGModuleCat.{u} S.obj} {r : PrimeSpectrum R} (D : Complete R S N r)
    (i : Fin (D.last + 1)) :
    (D.stage i).p.asIdeal =
        Ideal.map (algebraMap R (D.stage i).B) r.asIdeal ∧
      Function.Bijective (D.stage i).fiberMap := sorry

end Complete

end Module.Devissage
