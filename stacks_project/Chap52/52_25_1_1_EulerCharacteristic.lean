/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap52.Situation_52_16_1
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Quasicoherent
public import Mathlib.RingTheory.Length

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u v

namespace AlgebraicGeometry

namespace AffineAlgebraizationSetup

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- The punctured closed fiber `U₀ = X₀ ×_X U` in an affine algebraization setup. -/
abbrev U₀ (S : AffineAlgebraizationSetup A) : S.Y.Opens :=
  S.y ⁻¹ᵁ S.U

/-- The punctured closed fiber is the inverse image of `U` in `X₀`. -/
theorem U₀_eq (S : AffineAlgebraizationSetup A) : S.U₀ = S.y ⁻¹ᵁ S.U := sorry

end AffineAlgebraizationSetup

/-- The affine-local setup for coherent triples: a Noetherian local ring `A` and a regular
element `f` in its maximal ideal. The associated `AffineAlgebraizationSetup` has
`I = (f)` and `a` equal to the maximal ideal, so its schemes and opens are `X`, `X₀`, `U`,
and `U₀`. -/
structure CoherentTripleSetup.{w} (A : Type w)
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A] where
  /-- The equation cutting out the closed fiber. -/
  f : A
  /-- The element `f` lies in the maximal ideal. -/
  f_mem_maximalIdeal : f ∈ IsLocalRing.maximalIdeal A
  /-- The element `f` is a nonzerodivisor. -/
  f_regular : IsRegular f

namespace CoherentTripleSetup

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

/-- Construct the affine-local setup from its regular element and source hypotheses. -/
def ofElement (f : A) (f_mem_maximalIdeal : f ∈ IsLocalRing.maximalIdeal A)
    (f_regular : IsRegular f) : CoherentTripleSetup A :=
  { f := f
    f_mem_maximalIdeal := f_mem_maximalIdeal
    f_regular := f_regular }

/-- `ofElement` retains the chosen element cutting out the closed fiber. -/
theorem ofElement_f (f : A) (f_mem_maximalIdeal : f ∈ IsLocalRing.maximalIdeal A)
    (f_regular : IsRegular f) :
    (ofElement f f_mem_maximalIdeal f_regular).f = f := sorry

/-- The principal ideal `(f)` lies in the maximal ideal of the setup. -/
theorem span_singleton_le_maximalIdeal (S : CoherentTripleSetup A) :
    Ideal.span {S.f} ≤ IsLocalRing.maximalIdeal A := sorry

/-- The affine algebraization setup with closed fiber `(f)` and closed point the maximal ideal. -/
def algebraization (S : CoherentTripleSetup A) : AffineAlgebraizationSetup A :=
  AffineAlgebraizationSetup.ofIdeals (Ideal.span {S.f})
    (IsLocalRing.maximalIdeal A) S.span_singleton_le_maximalIdeal

/-- The associated algebraization setup has closed-fiber ideal `(S.f)` and closed-point ideal
the maximal ideal. -/
theorem algebraization_spec (S : CoherentTripleSetup A) :
    S.algebraization.I = Ideal.span {S.f} ∧
      S.algebraization.a = IsLocalRing.maximalIdeal A := sorry

/-- The setup records exactly that `f` lies in the maximal ideal and is regular. -/
theorem source_spec (S : CoherentTripleSetup A) :
    S.f ∈ IsLocalRing.maximalIdeal A ∧ IsRegular S.f := sorry

end CoherentTripleSetup

namespace CoherentTripleSetup

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

/-- The closed fiber over the punctured spectrum, viewed as a morphism `U₀ ⟶ U`. -/
abbrev closedFiberOnU (S : CoherentTripleSetup A) :
    S.algebraization.U₀.toScheme ⟶ S.algebraization.U.toScheme :=
  S.algebraization.y ∣_ S.algebraization.U

/-- The image of `S.f` as a section of the structure sheaf of `U`. -/
def elementOnU (S : CoherentTripleSetup A) : Γ(S.algebraization.U.toScheme, ⊤) :=
  S.algebraization.U.ι.appTop
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv S.f)

/-- The restriction of `S.f` to an open `V ⊆ U`. -/
def elementOnUSection (S : CoherentTripleSetup A)
    (V : S.algebraization.U.toScheme.Opens) : Γ(S.algebraization.U.toScheme, V) :=
  S.algebraization.U.toScheme.presheaf.map V.leTop.op S.elementOnU

/-- The canonical ring map from `A` to the global sections of the closed fiber. -/
def specialFiberRingHom (S : CoherentTripleSetup A) :
    A →+* Γ(S.algebraization.Y, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ S.algebraization.y.appTop).hom

/-- Global sections of a module on `Y`, regarded as an `A`-module. -/
abbrev specialFiberSections (S : CoherentTripleSetup A)
    (M : S.algebraization.Y.Modules) : ModuleCat A :=
  (ModuleCat.restrictScalars S.specialFiberRingHom).obj (M.val.obj (.op ⊤))

/-- The `A`-linear map on global sections induced by a morphism of modules on `Y`. -/
def specialFiberLinearMap (S : CoherentTripleSetup A)
    {M N : S.algebraization.Y.Modules} (g : M ⟶ N) :
    S.specialFiberSections M →ₗ[A] S.specialFiberSections N :=
  ((ModuleCat.restrictScalars S.specialFiberRingHom).map
    (g.val.app (.op ⊤))).hom

end CoherentTripleSetup

/-- A coherent triple `(F, F₀, α)` on `U` and the closed fiber `Y`. The pullback of
`F` to `U₀` is the sheaf-theoretic realization of `F / fF`. -/
structure CoherentTriple.{w} {A : Type w}
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (S : CoherentTripleSetup A) where
  /-- The coherent module `F` on `U`. -/
  F : S.algebraization.U.toScheme.Modules
  /-- The coherent module `F₀` on the closed fiber `Y`. -/
  F₀ : S.algebraization.Y.Modules
  /-- Coherence of `F`. -/
  coherent_F : F.IsCoherent
  /-- Coherence of `F₀`. -/
  coherent_F₀ : F₀.IsCoherent
  /-- Multiplication by `f` is injective on every open of `F`. -/
  mul_f_injective : ∀ V, Function.Injective (F.smul (S.elementOnUSection V)).hom
  /-- The source isomorphism `α : F / fF ≅ F₀|_{U₀}`. -/
  α : (Scheme.Modules.pullback S.closedFiberOnU).obj F ≅
    F₀.restrict S.algebraization.U₀.ι

namespace CoherentTriple

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
variable {S : CoherentTripleSetup A}

/-- Construct a coherent triple from its sheaf-level modules, injectivity, and source
isomorphism. -/
def ofModules (F : S.algebraization.U.toScheme.Modules)
    (F₀ : S.algebraization.Y.Modules) (coherent_F : F.IsCoherent)
    (coherent_F₀ : F₀.IsCoherent)
    (mul_f_injective : ∀ V,
      Function.Injective (F.smul (S.elementOnUSection V)).hom)
    (α : (Scheme.Modules.pullback S.closedFiberOnU).obj F ≅
      F₀.restrict S.algebraization.U₀.ι) : CoherentTriple S :=
  { F := F
    F₀ := F₀
    coherent_F := coherent_F
    coherent_F₀ := coherent_F₀
    mul_f_injective := mul_f_injective
    α := α }

/-- A coherent triple has coherent source modules, with `f` acting injectively on `F`. -/
theorem source_spec (T : CoherentTriple S) :
    T.F.IsCoherent ∧ ∀ V,
      Function.Injective (T.F.smul (S.elementOnUSection V)).hom := sorry

/-- A choice `(F', α', α₀')` supplied by Lemma 52.25.1. It extends `F` to `X`,
identifies the restriction with `F`, and compares its closed-fiber pullback with `F₀`. -/
structure Comparison.{w} {A : Type w}
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {S : CoherentTripleSetup A} (T : CoherentTriple S) where
  /-- The coherent module `F'` on `X`. -/
  F' : S.algebraization.X.Modules
  /-- Coherence of `F'`. -/
  coherent_F' : F'.IsCoherent
  /-- The actual restriction isomorphism `α' : F'|_U ≅ F`. -/
  α' : F'.restrict S.algebraization.U.ι ≅ T.F
  /-- The comparison map `α₀' : F'/fF' ⟶ F₀` on the closed fiber. -/
  α₀' : (Scheme.Modules.pullback S.algebraization.y).obj F' ⟶ T.F₀
  /-- The base-change identification used to compare the two restrictions to `U₀`. -/
  baseChange :
    (Scheme.Modules.pullback S.closedFiberOnU).obj
        (F'.restrict S.algebraization.U.ι) ≅
      ((Scheme.Modules.pullback S.algebraization.y).obj F').restrict
        S.algebraization.U₀.ι
  /-- The equality `α ∘ (α' mod f) = α₀'|_{U₀}` under `baseChange`. -/
  compatible :
    (Scheme.Modules.pullback S.closedFiberOnU).map α'.hom ≫ T.α.hom =
      baseChange.hom ≫
        (Scheme.Modules.restrictFunctor S.algebraization.U₀.ι).map α₀'

namespace Comparison

/-- Construct comparison data from a coherent extension, restriction isomorphism,
closed-fiber map, and compatibility square. -/
def ofRestrictionData (T : CoherentTriple S) (F' : S.algebraization.X.Modules)
    (coherent_F' : F'.IsCoherent)
    (α' : F'.restrict S.algebraization.U.ι ≅ T.F)
    (α₀' : (Scheme.Modules.pullback S.algebraization.y).obj F' ⟶ T.F₀)
    (baseChange :
      (Scheme.Modules.pullback S.closedFiberOnU).obj
          (F'.restrict S.algebraization.U.ι) ≅
        ((Scheme.Modules.pullback S.algebraization.y).obj F').restrict
          S.algebraization.U₀.ι)
    (compatible :
      (Scheme.Modules.pullback S.closedFiberOnU).map α'.hom ≫ T.α.hom =
        baseChange.hom ≫
          (Scheme.Modules.restrictFunctor S.algebraization.U₀.ι).map α₀') : T.Comparison :=
  { F' := F'
    coherent_F' := coherent_F'
    α' := α'
    α₀' := α₀'
    baseChange := baseChange
    compatible := compatible }

/-- The `A`-linear map on global sections underlying `α₀'`. -/
abbrev α₀LinearMap (C : Comparison T) :
    S.specialFiberSections ((Scheme.Modules.pullback S.algebraization.y).obj C.F') →ₗ[A]
      S.specialFiberSections T.F₀ :=
  S.specialFiberLinearMap C.α₀'

/-- Comparison data satisfies coherence of `F'` and the required equality on `U₀`. -/
theorem source_spec (C : Comparison T) :
    C.F'.IsCoherent ∧
      (Scheme.Modules.pullback S.closedFiberOnU).map C.α'.hom ≫ T.α.hom =
        C.baseChange.hom ≫
          (Scheme.Modules.restrictFunctor S.algebraization.U₀.ι).map C.α₀' := sorry

/-- The kernel of `α₀'` on global sections has finite `A`-length. -/
theorem α₀'_kernel_finiteLength (C : Comparison T) :
    IsFiniteLength A
      (C.α₀LinearMap.ker : Submodule A
        (S.specialFiberSections
          ((Scheme.Modules.pullback S.algebraization.y).obj C.F'))) := sorry

/-- The cokernel of `α₀'` on global sections has finite `A`-length. -/
theorem α₀'_cokernel_finiteLength (C : Comparison T) :
    IsFiniteLength A (S.specialFiberSections T.F₀ ⧸ C.α₀LinearMap.range) := sorry

end Comparison

end CoherentTriple

namespace CoherentTriple.Comparison

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
variable {S : CoherentTripleSetup A} {T : CoherentTriple S}

/-- The comparison-dependent bridge value used to define the Euler characteristic. -/
noncomputable def eulerCharacteristic (C : T.Comparison) : ℤ :=
  ((Module.length A (S.specialFiberSections T.F₀ ⧸
    C.α₀LinearMap.range)).toNat : ℤ) -
    ((Module.length A C.α₀LinearMap.ker).toNat : ℤ)

/-- The Euler value of a comparison is the length of its cokernel minus the length of its
kernel. -/
theorem eulerCharacteristic_eq (C : T.Comparison) :
    C.eulerCharacteristic =
      ((Module.length A (S.specialFiberSections T.F₀ ⧸
        C.α₀LinearMap.range)).toNat : ℤ) -
        ((Module.length A C.α₀LinearMap.ker).toNat : ℤ) := sorry

end CoherentTriple.Comparison

end AlgebraicGeometry
