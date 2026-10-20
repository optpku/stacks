/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Adjunction
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections.Pushforward
import Mathlib.Tactic.CrossRefAttribute

/-!
# Change of space through the scalar-extension adjunction

The canonical change-of-space map is linear over `Γ(Y, 𝒪_Y)` after restricting the scalars
on its target.  Its adjoint is a genuinely `Γ(X, 𝒪_X)`-linear map whose source is derived
extension of scalars.  Keeping both forms prevents the semilinear textbook notation from being
misread as an action of `Γ(X, 𝒪_X)` on `RΓ(Y, G)` itself.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections.Adjoint

variable {X Y : RingedSpace.{u}}

/-- The homomorphism on global section rings induced by a morphism of ringed spaces. -/
@[stacks 01F9 "global-section scalar map", stacks 01FD "global-section scalar map"]
abbrev scalarMap (f : X ⟶ Y) :
    globalSectionsRing Y →+* globalSectionsRing X :=
  (sectionsMapOnOpen f ⊤).hom

/-- Derived global sections on `Y`, extended to modules over `Γ(X, 𝒪_X)`. -/
@[stacks 01F9 "scalar-extended derived global sections",
  stacks 01FD "scalar-extended derived global sections"]
abbrev extended (f : X ⟶ Y) (L : DerivedCategory Y.Modules) :
    DerivedCategory (ModuleCat (globalSectionsRing X)) :=
  (ModuleCat.derivedExtensionOfScalars (scalarMap f)).obj
    ((GlobalSections.functor Y).obj L)

/-- The `Γ(X, 𝒪_X)`-linear adjoint of the restricted-scalar change-of-space map induced
by a morphism into derived pushforward. -/
@[stacks 01F9 "scalar-extended derived global-sections map",
  stacks 01FD "scalar-extended derived global-sections map"]
noncomputable def mapOfPushforward (f : X ⟶ Y)
    {K : DerivedCategory X.Modules} {L : DerivedCategory Y.Modules}
    (α : L ⟶ (moduleDerivedPushforward f).obj K) :
    extended f L ⟶ (GlobalSections.functor X).obj K :=
  (ModuleCat.derivedExtensionRestrictionHomEquiv
    (scalarMap f) ((GlobalSections.functor Y).obj L)
      ((GlobalSections.functor X).obj K)).symm
    (GlobalSections.mapOfPushforward f α)

/-- The `Γ(X, 𝒪_X)`-linear adjoint of the change-of-space map induced by an `f`-map. -/
@[stacks 01F9 "scalar-extended derived global-sections map of an f-map",
  stacks 01FD "scalar-extended derived global-sections map of an f-map"]
noncomputable def mapOfFMap (f : X ⟶ Y) {G : Y.Modules} {F : X.Modules}
    (φ : G ⟶ (RingedSpace.Hom.pushforward f).obj F) :
    extended f ((DerivedCategory.singleFunctor Y.Modules 0).obj G) ⟶
      (GlobalSections.functor X).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj F) :=
  mapOfPushforward f (moduleDerivedPushforward.comparison f G F φ)

/-- Transposing `mapOfPushforward` back across extension/restriction of scalars recovers the
canonical restricted-scalar map. -/
@[stacks 01F9 "scalar-extension adjunction specification",
  stacks 01FD "scalar-extension adjunction specification"]
theorem mapOfPushforward_adjunct (f : X ⟶ Y)
    {K : DerivedCategory X.Modules} {L : DerivedCategory Y.Modules}
    (α : L ⟶ (moduleDerivedPushforward f).obj K) :
    ModuleCat.derivedExtensionRestrictionHomEquiv
        (scalarMap f) ((GlobalSections.functor Y).obj L)
          ((GlobalSections.functor X).obj K) (mapOfPushforward f α) =
      GlobalSections.mapOfPushforward f α := sorry

/-- Transposing the adjoint `f`-map back to restricted scalars recovers the canonical
change-of-space map of the `f`-map. -/
@[stacks 01F9 "scalar-extended f-map adjunction specification",
  stacks 01FD "scalar-extended f-map adjunction specification"]
theorem mapOfFMap_adjunct
    (f : X ⟶ Y) {G : Y.Modules} {F : X.Modules}
    (φ : G ⟶ (RingedSpace.Hom.pushforward f).obj F) :
    ModuleCat.derivedExtensionRestrictionHomEquiv
        (scalarMap f)
          ((GlobalSections.functor Y).obj
            ((DerivedCategory.singleFunctor Y.Modules 0).obj G))
          ((GlobalSections.functor X).obj
            ((DerivedCategory.singleFunctor X.Modules 0).obj F))
          (mapOfFMap f φ) =
      GlobalSections.mapOfFMap f φ := sorry

/-- The scalar-extended change-of-space construction is natural in a commutative square of
morphisms into derived pushforward. -/
@[stacks 01F9 "naturality of scalar-extended derived global sections",
  stacks 01FD "naturality of scalar-extended derived global sections"]
theorem mapOfPushforward_natural (f : X ⟶ Y)
    {K K' : DerivedCategory X.Modules} {L L' : DerivedCategory Y.Modules}
    (α : L ⟶ (moduleDerivedPushforward f).obj K)
    (α' : L' ⟶ (moduleDerivedPushforward f).obj K')
    (a : L ⟶ L') (b : K ⟶ K')
    (h : α ≫ (moduleDerivedPushforward f).map b = a ≫ α') :
    (ModuleCat.derivedExtensionOfScalars (scalarMap f)).map
          ((GlobalSections.functor Y).map a) ≫ mapOfPushforward f α' =
      mapOfPushforward f α ≫ (GlobalSections.functor X).map b := sorry

/-- The adjoint `f`-map entry point is the specialization of the derived-pushforward entry
point along the canonical single-complex comparison. -/
@[stacks 01F9 "scalar-extended f-map coherence",
  stacks 01FD "scalar-extended f-map coherence"]
theorem mapOfFMap_eq_mapOfPushforward
    (f : X ⟶ Y) {G : Y.Modules} {F : X.Modules}
    (φ : G ⟶ (RingedSpace.Hom.pushforward f).obj F) :
    mapOfFMap f φ =
      mapOfPushforward f (moduleDerivedPushforward.comparison f G F φ) := sorry

end AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections.Adjoint
