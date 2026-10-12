/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Cohomology
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Tensor
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Tactic.CrossRefAttribute

/-!
# Induced maps after derived tensor with a sheaf

On a ringed site, cohomological connectivity of a morphism in `D⁻(𝒪)` is preserved by
derived tensor with a sheaf of `𝒪`-modules placed in degree zero.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open ComplexShape
open DerivedCategory
open RingedSite (ModuleCat)
open RingedSite.Hom (ModuleDerived)
open scoped CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u v w

namespace RingedSite.Hom.ModuleDerived

-- Local instance justification (defeq pin): `moduleCat_hasDerivedCategory` is reducible to `HasDerivedCategory.standard` and is not global; `ModuleDerived`, `cohomologySheafMap`, `singleFunctor`, and `DerivedTensor.Right.functor` must share that same derived-category instance.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory

section

variable {X : RingedSite.{u, v, w}} [UnivLE.{max u v, w}]
variable [MonoidalCategory (ModuleCat.{w} X)] [MonoidalPreadditive (ModuleCat.{w} X)]
variable [∀ (K L : CochainComplex (ModuleCat.{w} X) ℤ),
  HomologicalComplex.HasMapBifunctor K L (curriedTensor (ModuleCat.{w} X)) (up ℤ)]
variable [DerivedTensor.Right.Has (C := ModuleCat.{w} X)]

/-- The morphism `α ⊗ᴸ id_F` obtained by applying the fixed-right derived tensor functor at
the degree-zero single of a sheaf `F` of `𝒪`-modules. -/
noncomputable abbrev tensorRightHom (F : ModuleCat.{w} X) {K L : ModuleDerived.{w} X}
    (α : K ⟶ L) :
    K ⊗ᴸ (singleFunctor (ModuleCat.{w} X) (0 : ℤ)).obj F ⟶
      L ⊗ᴸ (singleFunctor (ModuleCat.{w} X) (0 : ℤ)).obj F :=
  (DerivedTensor.Right.functor
    ((singleFunctor (ModuleCat.{w} X) (0 : ℤ)).obj F)).map α

/-- Lemma 91.16.3 (1): if `α : K ⟶ L` in `D⁻(𝒪)` on a ringed site `X` has `H^i(α)` an
isomorphism for all `i ≥ n`, then `H^i(α ⊗ᴸ id_F)` is an isomorphism for all `i ≥ n`, for
any sheaf `F` of `𝒪`-modules. `D⁻(𝒪)` is encoded by `ModuleDerived` objects with `IsLE`,
`H^i(α)` by `cohomologySheafMap`, and `α ⊗ᴸ id_F` by `tensorRightHom`. -/
@[stacks 0DIV]
theorem derivedTensor_homologyMap_isIso
    {K L : ModuleDerived.{w} X} {a b : ℤ} [K.IsLE a] [L.IsLE b]
    (α : K ⟶ L) (F : ModuleCat.{w} X) (n : ℤ)
    (hα : ∀ j, n ≤ j → IsIso (cohomologySheafMap X j α))
    (i : ℤ) (hi : n ≤ i) :
    IsIso (cohomologySheafMap X i (tensorRightHom F α)) := sorry

/-- Lemma 91.16.3 (2): if `α : K ⟶ L` in `D⁻(𝒪)` on a ringed site `X` has `H^i(α)` an
isomorphism for all `i > n` and an epimorphism for `i = n`, then `H^i(α ⊗ᴸ id_F)` is an
isomorphism for all `i > n` and an epimorphism for `i = n`. `D⁻(𝒪)` is encoded by
`ModuleDerived` objects with `IsLE`, `H^i(α)` by `cohomologySheafMap`, and `α ⊗ᴸ id_F` by
`tensorRightHom`. -/
@[stacks 0DIV]
theorem derivedTensor_homologyMap_isIso_and_epi
    {K L : ModuleDerived.{w} X} {a b : ℤ} [K.IsLE a] [L.IsLE b]
    (α : K ⟶ L) (F : ModuleCat.{w} X) (n : ℤ)
    (hα_iso : ∀ j, n < j → IsIso (cohomologySheafMap X j α))
    (hα_epi : Epi (cohomologySheafMap X n α)) :
    (∀ i, n < i → IsIso (cohomologySheafMap X i (tensorRightHom F α))) ∧
      Epi (cohomologySheafMap X n (tensorRightHom F α)) := sorry

end

end RingedSite.Hom.ModuleDerived
