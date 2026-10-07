module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.OpenSubsetExtensionByInitial
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Stalk
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.OpenSubset
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Stalk
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Extension by an initial object for module sheaves on open subspaces

This module lifts the generic open-subspace extension-by-initial-object construction to presheaves
and sheaves of modules, including the adjunction and its compatibility with restriction.
-/

@[expose] public section

open CategoryTheory Opposite TopCat TopologicalSpace
open CategoryTheory.Limits
open TopCat.Opens.Subspace

noncomputable section

universe w u

namespace SheafOfModules.OpenSubset.ExtensionByZero

/-- The sheaf-level extension-by-zero functor on modules along the open inclusion `U ↪ X`.

It is obtained by applying `PresheafOfModules.OpenSubset.ExtensionByZero.functor` followed by
module sheafification. -/
@[stacks 00A4 "sheaf of modules extension by zero"]
noncomputable abbrev functor
    {X : TopCat.{u}} (U : Opens X) (𝒪 : X.Sheaf RingCat.{u}) :
    SheafOfModules ((TopCat.Sheaf.pullback RingCat (inclusion U)).obj 𝒪) ⥤
      SheafOfModules 𝒪 :=
  SheafOfModules.forget
      ((TopCat.Sheaf.pullback RingCat (inclusion U)).obj 𝒪) ⋙
    PresheafOfModules.OpenSubset.ExtensionByZero.functor U
      ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat
        (inclusion U)).unit.app 𝒪).hom ⋙
    PresheafOfModules.sheafification (R := 𝒪) (R₀ := 𝒪.obj) (α := 𝟙 𝒪.obj)

end SheafOfModules.OpenSubset.ExtensionByZero

namespace SheafOfModules.OpenSubset.ExtensionByZero

variable {X : TopCat.{w}}

section Modules

/-- The coefficient-ring mate induced by the open-embedding comparison for module sheaves.

It packages the pullback-pushforward unit, the sheaf-pullback comparison, and their two mate
identities for use by the module-presheaf extension-by-zero API. -/
noncomputable def openEmbeddingRingMapMate
    (U : Opens X) (𝒪 : X.Sheaf RingCat.{w}) :
    PresheafOfModules.OpenSubset.ExtensionByZero.RingMapMate U 𝒪.obj
      ((TopCat.Sheaf.pullback RingCat.{w} (inclusion U)).obj 𝒪).obj where
  toPushforward :=
    ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{w}
      (inclusion U)).unit.app 𝒪).hom
  toPullback := ((U.isOpenEmbedding.sheafPullbackIso RingCat.{w}).app 𝒪).hom.hom
  counit_eq := SheafOfModules.OpenSubset.Restriction.openEmbeddingCounitEq U 𝒪
  unit_eq := SheafOfModules.OpenSubset.Restriction.openEmbeddingUnitEq U 𝒪

/-- The Hom equivalence for module-sheaf extension by zero against the concrete open-embedding
restriction model, before comparison with mathlib's chosen module pullback. -/
noncomputable def openEmbeddingHomEquiv
    (U : Opens X) (𝒪 : X.Sheaf RingCat.{w})
    (ℱ : SheafOfModules
      ((TopCat.Sheaf.pullback RingCat.{w}
        (inclusion U)).obj 𝒪))
    (𝒢 : SheafOfModules 𝒪) :
    ((functor U 𝒪).obj ℱ ⟶ 𝒢) ≃
      (ℱ ⟶
        (SheafOfModules.OpenSubset.Restriction.openEmbeddingFunctor U 𝒪).obj 𝒢) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 𝒪.obj)).homEquiv
      ((PresheafOfModules.OpenSubset.ExtensionByZero.functor U
        (openEmbeddingRingMapMate U 𝒪).toPushforward).obj ℱ.val) 𝒢).trans
    ((PresheafOfModules.OpenSubset.ExtensionByZero.RingMapMate.homEquiv
      (openEmbeddingRingMapMate U 𝒪) ℱ.val 𝒢.val).trans
        (((SheafOfModules.fullyFaithfulForget
            ((TopCat.Sheaf.pullback RingCat.{w}
              (inclusion U)).obj 𝒪)).homEquiv :
          (ℱ ⟶
              (SheafOfModules.OpenSubset.Restriction.openEmbeddingFunctor U 𝒪).obj 𝒢) ≃
            (ℱ.val ⟶
              ((SheafOfModules.OpenSubset.Restriction.openEmbeddingFunctor U 𝒪).obj 𝒢).val)).symm))

/-- Module-sheaf extension by zero is left adjoint to the concrete restriction model obtained
from the open embedding. -/
@[stacks 00A5 "open-embedding module extension-restriction adjunction"]
noncomputable def openEmbeddingAdjunction
    (U : Opens X) (𝒪 : X.Sheaf RingCat.{w}) :
    functor U 𝒪 ⊣
      SheafOfModules.OpenSubset.Restriction.openEmbeddingFunctor U 𝒪 :=
  Adjunction.mkOfHomEquiv
    { homEquiv := openEmbeddingHomEquiv U 𝒪
      homEquiv_naturality_left_symm := sorry
      homEquiv_naturality_right := sorry }

/-- Module-sheaf extension by zero is canonically left adjoint to mathlib's module restriction
functor along an open-subspace inclusion. -/
@[stacks 00A5 "module extension-restriction adjunction"]
noncomputable def adjunction
    (U : Opens X) (𝒪 : X.Sheaf RingCat.{w}) :
    functor U 𝒪 ⊣
      SheafOfModules.pullback
        ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{w}
          (inclusion U)).unit.app 𝒪) :=
  (openEmbeddingAdjunction U 𝒪).ofNatIsoRight
    (SheafOfModules.OpenSubset.Restriction.openEmbeddingIso U 𝒪)

/-- Outside an open subset, the stalk module of extension by zero is zero. -/
@[stacks 00A5 "stalk of module extension by zero outside the open subset"]
theorem stalk_isZero_of_not_mem
    (U : Opens X) (𝒪 : X.Sheaf RingCat.{w})
    (ℱ : SheafOfModules
      ((TopCat.Sheaf.pullback RingCat.{w} (inclusion U)).obj 𝒪))
    {x : X} (hx : x ∉ (U : Set X)) :
    IsZero ((SheafOfModules.stalkFunctor 𝒪 x).obj
      ((functor U 𝒪).obj ℱ)) := sorry

/-- The unit of any module extension-by-zero adjunction is an isomorphism on stalk modules over
the open subspace. -/
theorem unit_stalk_isIso_of_adj
    (U : Opens X) (𝒪 : X.Sheaf RingCat.{w})
    (adj : functor U 𝒪 ⊣
      SheafOfModules.pullback
        ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{w}
          (inclusion U)).unit.app 𝒪))
    (ℱ : SheafOfModules
      ((TopCat.Sheaf.pullback RingCat.{w} (inclusion U)).obj 𝒪))
    (x : space U) :
    IsIso
      ((SheafOfModules.stalkFunctor
        ((TopCat.Sheaf.pullback RingCat.{w} (inclusion U)).obj 𝒪) x).map
        (adj.unit.app ℱ)) := sorry

/-- The unit of the canonical module extension-by-zero adjunction is an isomorphism on stalk
modules over the open subspace. -/
@[stacks 00A5 "stalk of module extension by zero inside the open subset", instance]
theorem unit_stalk_isIso
    (U : Opens X) (𝒪 : X.Sheaf RingCat.{w})
    (ℱ : SheafOfModules
      ((TopCat.Sheaf.pullback RingCat.{w} (inclusion U)).obj 𝒪))
    (x : space U) :
    IsIso
      ((SheafOfModules.stalkFunctor
        ((TopCat.Sheaf.pullback RingCat.{w} (inclusion U)).obj 𝒪) x).map
        ((adjunction U 𝒪).unit.app ℱ)) := sorry

/-- The unit of any adjunction from module extension by zero to open-subspace restriction is an
isomorphism. -/
theorem unit_isIso_of_adj
    (U : Opens X) (𝒪 : X.Sheaf RingCat.{w})
    (adj : functor U 𝒪 ⊣
      SheafOfModules.pullback
        ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{w}
          (inclusion U)).unit.app 𝒪)) :
    IsIso adj.unit := sorry

/-- Restriction after the canonical module extension by zero is naturally isomorphic to the
identity. -/
@[stacks 00A5 "module restriction after extension by zero", instance]
theorem unit_isIso
    (U : Opens X) (𝒪 : X.Sheaf RingCat.{w}) :
    IsIso (adjunction U 𝒪).unit := sorry

/-- Module extension by zero along an open inclusion is fully faithful.

Unlike the generic `j! U`, this is the module-sheaf functor over the pullback ring sheaf; its
adjunction and essential-image API retain the scalar-ring and stalk-module structure. -/
@[stacks 00A5 "module extension by zero is fully faithful"]
noncomputable def fullyFaithful
    (U : Opens X) (𝒪 : X.Sheaf RingCat.{w}) :
    (functor U 𝒪).FullyFaithful :=
  (adjunction U 𝒪).fullyFaithfulLOfIsIsoUnit

/-- The canonical module extension-by-zero functor is full. -/
noncomputable instance functor_full
    (U : Opens X) (𝒪 : X.Sheaf RingCat.{w}) :
    (functor U 𝒪).Full :=
  (fullyFaithful U 𝒪).full

/-- The canonical module extension-by-zero functor is faithful. -/
noncomputable instance functor_faithful
    (U : Opens X) (𝒪 : X.Sheaf RingCat.{w}) :
    (functor U 𝒪).Faithful :=
  (fullyFaithful U 𝒪).faithful

/-- A sheaf of modules lies in the essential image of extension by zero from `U` exactly when
all stalk modules away from `U` vanish. -/
theorem essImage_iff
    (U : Opens X) (𝒪 : X.Sheaf RingCat.{w}) (𝒢 : SheafOfModules 𝒪) :
    (functor U 𝒪).essImage 𝒢 ↔
      ∀ x : X, x ∉ (U : Set X) →
        IsZero ((SheafOfModules.stalkFunctor 𝒪 x).obj 𝒢) := sorry

end Modules

end SheafOfModules.OpenSubset.ExtensionByZero
