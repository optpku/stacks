/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.ObjectProperty.Basic
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import ReasLib.Algebra.Module.Bimodule.RelativeTensor
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalLeftDerived

/-!
# Finite Tor-dimension over a possibly noncommutative ring

Relative tensor of a right module against a left module, its total left derived functor into
`DerivedCategory (ModuleCat ℤ)`, and the resulting Tor-amplitude predicates on
`DerivedCategory (ModuleCat R)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape
open Module.Bimodule

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.RelativeTensor

variable {R : Type u} [Ring R]

/-- The abelian group underlying the relative tensor of a right `R`-module with a left
`R`-module. -/
abbrev relativeTensor (N : ModuleCat.{u} Rᵐᵒᵖ) (K : ModuleCat.{u} R) : Type u :=
  RelativeTensor.Product (R := ℤ) (A := R) (M := (N : Type u)) (N := (K : Type u))

/-- A pure tensor in `relativeTensor N K`. -/
def relativeTmul (N : ModuleCat.{u} Rᵐᵒᵖ) (K : ModuleCat.{u} R) (n : N) (k : K) :
    relativeTensor N K :=
  RelativeTensor.tmul (R := ℤ) (A := R) (M := (N : Type u)) (N := (K : Type u)) n k

/-- Balancing relations for `relativeTensor N K`. -/
abbrev relativeTensorRelations (N : ModuleCat.{u} Rᵐᵒᵖ) (K : ModuleCat.{u} R) :=
  RelativeTensor.relations (R := ℤ) (A := R) (M := (N : Type u)) (N := (K : Type u))

/-- A left `R`-linear map in the second factor preserves relative tensor relations. -/
theorem tensorWithRightLinear_relations (N : ModuleCat.{u} Rᵐᵒᵖ)
    {K L : ModuleCat.{u} R} (f : K ⟶ L) :
    relativeTensorRelations N K ≤
      Submodule.comap (TensorProduct.map LinearMap.id (f.hom.restrictScalars ℤ))
        (relativeTensorRelations N L) := sorry

/-- The ℤ-linear map on relative tensors induced by a left `R`-linear map in the second
factor. -/
def tensorWithRightLinear (N : ModuleCat.{u} Rᵐᵒᵖ) {K L : ModuleCat.{u} R} (f : K ⟶ L) :
    relativeTensor N K →ₗ[ℤ] relativeTensor N L :=
  (relativeTensorRelations N K).mapQ (relativeTensorRelations N L)
    (TensorProduct.map LinearMap.id (f.hom.restrictScalars ℤ))
    (tensorWithRightLinear_relations N f)

/-- Evaluation of `tensorWithRightLinear` on a pure relative tensor. -/
theorem tensorWithRightLinear_tmul (N : ModuleCat.{u} Rᵐᵒᵖ) {K L : ModuleCat.{u} R}
    (f : K ⟶ L) (n : N) (k : K) :
    tensorWithRightLinear N f (relativeTmul N K n k) =
      relativeTmul N L n (f.hom k) := sorry

/-- Relative tensor with a fixed right module preserves identity morphisms. -/
theorem tensorWithRight_map_id (N : ModuleCat.{u} Rᵐᵒᵖ) (K : ModuleCat.{u} R) :
    ModuleCat.ofHom (tensorWithRightLinear N (𝟙 K)) =
      𝟙 (ModuleCat.of ℤ (relativeTensor N K)) := sorry

/-- Relative tensor with a fixed right module preserves composition of morphisms. -/
theorem tensorWithRight_map_comp (N : ModuleCat.{u} Rᵐᵒᵖ)
    {K L M : ModuleCat.{u} R} (f : K ⟶ L) (g : L ⟶ M) :
    ModuleCat.ofHom (tensorWithRightLinear N (f ≫ g)) =
      ModuleCat.ofHom (tensorWithRightLinear N f) ≫
        ModuleCat.ofHom (tensorWithRightLinear N g) := sorry

/-- Relative tensor with a fixed right `R`-module, as a functor on left `R`-modules valued in
abelian groups. -/
def tensorWithRight (N : ModuleCat.{u} Rᵐᵒᵖ) :
    ModuleCat.{u} R ⥤ ModuleCat.{u} ℤ where
  obj K := ModuleCat.of ℤ (relativeTensor N K)
  map f := ModuleCat.ofHom (tensorWithRightLinear N f)
  map_id := tensorWithRight_map_id N
  map_comp := tensorWithRight_map_comp N

/-- On objects, `tensorWithRight N` is the relative tensor abelian group. -/
theorem tensorWithRight_obj (N : ModuleCat.{u} Rᵐᵒᵖ) (K : ModuleCat.{u} R) :
    (tensorWithRight N).obj K = ModuleCat.of ℤ (relativeTensor N K) := sorry

/-- On morphisms, `tensorWithRight N` is `tensorWithRightLinear`. -/
theorem tensorWithRight_map (N : ModuleCat.{u} Rᵐᵒᵖ) {K L : ModuleCat.{u} R}
    (f : K ⟶ L) :
    (tensorWithRight N).map f = ModuleCat.ofHom (tensorWithRightLinear N f) := sorry

/-- Relative tensor with a fixed right module is an additive functor. -/
instance tensorWithRight.instAdditive (N : ModuleCat.{u} Rᵐᵒᵖ) :
    (tensorWithRight N).Additive := sorry

/-- The homotopy-to-derived functor of `tensorWithRight N` admits a total left derived
functor. -/
instance tensorWithRight.instHasLeftDerivedFunctor (N : ModuleCat.{u} Rᵐᵒᵖ) :
    (Functor.Homotopy.toDerived (tensorWithRight N)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (ModuleCat.{u} R) (up ℤ)) := sorry

/-- Total left derived functor of relative tensor with a fixed right `R`-module. -/
def derivedTensorWithRight (N : ModuleCat.{u} Rᵐᵒᵖ) :
    DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} ℤ) :=
  Functor.LeftDerived.Homotopy.functor (tensorWithRight N)

/-- The derived relative tensor of a right module `N` with `K`, as an object of
`DerivedCategory (ModuleCat ℤ)`. -/
def derivedTensorRight (N : ModuleCat.{u} Rᵐᵒᵖ)
    (K : DerivedCategory (ModuleCat.{u} R)) :
    DerivedCategory (ModuleCat.{u} ℤ) :=
  (derivedTensorWithRight N).obj K

/-- Objectwise form of the total left derived relative tensor. -/
theorem derivedTensorRight_obj (N : ModuleCat.{u} Rᵐᵒᵖ)
    (K : DerivedCategory (ModuleCat.{u} R)) :
    derivedTensorRight N K = (derivedTensorWithRight N).obj K := sorry

/-- An object of `DerivedCategory (ModuleCat R)` has Tor-amplitude in `Set.Icc a b` when
`derivedTensorRight N K` has vanishing homology outside that interval for every right
`R`-module `N`. -/
def HasTorAmplitudeIn (K : DerivedCategory (ModuleCat.{u} R)) (a b : ℤ) : Prop :=
  ∀ (N : ModuleCat.{u} Rᵐᵒᵖ) (i : ℤ), i ∉ Set.Icc a b →
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} ℤ) i).obj
      (derivedTensorRight N K))

/-- The object property of having Tor-amplitude in a fixed finite interval. -/
def torAmplitudeIn (a b : ℤ) : ObjectProperty (DerivedCategory (ModuleCat.{u} R)) :=
  fun K ↦ HasTorAmplitudeIn K a b

/-- Membership in `torAmplitudeIn a b` is `HasTorAmplitudeIn`. -/
theorem torAmplitudeIn_iff (K : DerivedCategory (ModuleCat.{u} R)) (a b : ℤ) :
    torAmplitudeIn a b K ↔ HasTorAmplitudeIn K a b := sorry

/-- `HasTorAmplitudeIn K a b` is homology vanishing of `derivedTensorRight N K` outside
`Set.Icc a b`. -/
theorem hasTorAmplitudeIn_iff_homology (K : DerivedCategory (ModuleCat.{u} R))
    (a b : ℤ) :
    HasTorAmplitudeIn K a b ↔
      ∀ (N : ModuleCat.{u} Rᵐᵒᵖ) (i : ℤ), i ∉ Set.Icc a b →
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} ℤ) i).obj
          (derivedTensorRight N K)) := sorry

/-- The object property of having some finite Tor-amplitude interval. -/
def finiteTorDimension : ObjectProperty (DerivedCategory (ModuleCat.{u} R)) :=
  fun K ↦ ∃ a b : ℤ, HasTorAmplitudeIn K a b

/-- An object of `DerivedCategory (ModuleCat R)` has finite Tor-dimension when some finite
interval is a Tor-amplitude interval. -/
abbrev HasFiniteTorDimension (K : DerivedCategory (ModuleCat.{u} R)) : Prop :=
  finiteTorDimension K

/-- Finite Tor-dimension is the existence of a finite Tor-amplitude interval. -/
theorem hasFiniteTorDimension_iff (K : DerivedCategory (ModuleCat.{u} R)) :
    HasFiniteTorDimension K ↔ ∃ a b : ℤ, HasTorAmplitudeIn K a b := sorry

/-- Tor-amplitude in a fixed interval implies finite Tor-dimension. -/
theorem HasTorAmplitudeIn.hasFiniteTorDimension
    {K : DerivedCategory (ModuleCat.{u} R)} {a b : ℤ}
    (hK : HasTorAmplitudeIn K a b) :
    HasFiniteTorDimension K := sorry

/-- Tor-amplitude in a fixed interval is invariant under isomorphism in
`DerivedCategory (ModuleCat R)`. -/
theorem HasTorAmplitudeIn.ofIso {K L : DerivedCategory (ModuleCat.{u} R)} {a b : ℤ}
    (hK : HasTorAmplitudeIn K a b) (e : K ≅ L) :
    HasTorAmplitudeIn L a b := sorry

/-- Finite Tor-dimension is invariant under isomorphism in
`DerivedCategory (ModuleCat R)`. -/
theorem HasFiniteTorDimension.ofIso {K L : DerivedCategory (ModuleCat.{u} R)}
    (hK : HasFiniteTorDimension K) (e : K ≅ L) :
    HasFiniteTorDimension L := sorry

/-- Finite Tor-dimension implies there are `a, b : ℤ` with `K.IsGE a` and `K.IsLE b`. -/
theorem HasFiniteTorDimension.exists_isGE_isLE
    {K : DerivedCategory (ModuleCat.{u} R)} (hK : HasFiniteTorDimension K) :
    ∃ a b : ℤ, K.IsGE a ∧ K.IsLE b := sorry

end CategoryTheory.DerivedCategory.RelativeTensor

end
