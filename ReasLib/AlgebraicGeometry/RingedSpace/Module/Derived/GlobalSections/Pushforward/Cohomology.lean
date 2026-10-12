/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections.Pushforward.Bounded
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Adjunction
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Homology
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cohomology maps induced by an f-map

Applying homology to the bounded change-of-space map produces a morphism of
`Γ(Y, 𝒪_Y)`-modules.  The restriction of scalars in the target is retained, so this owner is
strictly stronger than the underlying additive-group map.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections.Bounded

variable {X Y : RingedSpace.{u}}

/-- Degree-`i` homology of bounded-below derived global sections. -/
@[stacks 01FA "bounded derived global-sections homology"]
abbrev homology (X : RingedSpace.{u})
    (K : DerivedCategory.Plus X.Modules) (i : ℤ) :=
  (DerivedCategory.Plus.homologyFunctor
    (ModuleCat (globalSectionsRing X)) i).obj ((functor X).obj K)

/-- Degree-`i` homology of bounded-below derived global sections on `X`, with scalars restricted
to the global-section ring of `Y`. -/
@[stacks 01FA "restricted bounded derived global-sections homology"]
abbrev restrictedHomology (f : X ⟶ Y)
    (K : DerivedCategory.Plus X.Modules) (i : ℤ) :=
  (DerivedCategory.Plus.homologyFunctor
    (ModuleCat (globalSectionsRing Y)) i).obj ((restricted f).obj K)

/-- Degree-`i` cohomology of a module sheaf, computed by bounded-below derived global sections. -/
@[stacks 01FA "module-valued sheaf cohomology"]
abbrev cohomology (X : RingedSpace.{u}) (F : X.Modules) (i : ℕ) :=
  homology X ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj F) (i : ℤ)

/-- Degree-`i` cohomology on `X`, with scalars restricted to `Γ(Y, 𝒪_Y)`. -/
@[stacks 01FA "restricted module-valued sheaf cohomology"]
abbrev restrictedCohomology (f : X ⟶ Y) (F : X.Modules) (i : ℕ) :=
  restrictedHomology f
    ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj F) (i : ℤ)

/-- A morphism into bounded-below derived pushforward induces the map on homology of derived
global sections. -/
@[stacks 01FA "homology map from a derived f-map"]
noncomputable def homologyMapOfPushforward (f : X ⟶ Y)
    {K : DerivedCategory.Plus X.Modules} {L : DerivedCategory.Plus Y.Modules}
    (α : L ⟶ (moduleDerivedPushforwardPlus f).obj K) (i : ℤ) :
    homology Y L i ⟶ restrictedHomology f K i :=
  (DerivedCategory.Plus.homologyFunctor
    (ModuleCat (globalSectionsRing Y)) i).map (mapOfPushforward f α)

/-- An `f`-map induces the map on integral-degree homology of bounded-below derived global
sections. -/
@[stacks 01FA "homology map of an f-map"]
noncomputable def homologyMapOfFMap (f : X ⟶ Y)
    {G : Y.Modules} {F : X.Modules}
    (φ : G ⟶ (RingedSpace.Hom.pushforward f).obj F) (i : ℤ) :
    homology Y ((DerivedCategory.Plus.singleFunctor Y.Modules 0).obj G) i ⟶
      restrictedHomology f
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj F) i :=
  (DerivedCategory.Plus.homologyFunctor
    (ModuleCat (globalSectionsRing Y)) i).map (mapOfFMap f φ)

/-- Equation 20.14.1.2 / Tag 01FA: an `f`-map `G ⟶ f_* F` induces the canonical
`Γ(Y, 𝒪_Y)`-linear map `H^i(Y, G) ⟶ H^i(X, F)`, where target scalars are restricted
along `Γ(Y, 𝒪_Y) ⟶ Γ(X, 𝒪_X)`. -/
@[stacks 01FA "cohomology map of an f-map"]
noncomputable def cohomologyMapOfFMap (f : X ⟶ Y)
    {G : Y.Modules} {F : X.Modules}
    (φ : G ⟶ (RingedSpace.Hom.pushforward f).obj F) (i : ℕ) :
    cohomology Y G i ⟶ restrictedCohomology f F i :=
  homologyMapOfFMap f φ (i : ℤ)

/-- The cohomology map is the nonnegative-degree specialization of the integral homology map. -/
@[stacks 01FA "cohomology map of an f-map formula"]
theorem cohomologyMapOfFMap_eq (f : X ⟶ Y)
    {G : Y.Modules} {F : X.Modules}
    (φ : G ⟶ (RingedSpace.Hom.pushforward f).obj F) (i : ℕ) :
    cohomologyMapOfFMap f φ i = homologyMapOfFMap f φ (i : ℤ) := sorry

end AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections.Bounded

namespace AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

variable {T' T : RingedSpace.{u}}

/-- Restriction of scalars commutes canonically with homology of derived modules. -/
noncomputable abbrev restrictionHomologyIso (a : T' ⟶ T)
    (K : DerivedCategory (ModuleCat
      (RingedSpace.sectionsRingOnOpen T' (RingedSpace.preimageOpen a ⊤)))) (n : ℤ) :
    (RingedSpace.moduleSectionsRestrictionFunctor a ⊤).obj
        ((DerivedCategory.homologyFunctor
          (ModuleCat (RingedSpace.sectionsRingOnOpen T'
            (RingedSpace.preimageOpen a ⊤))) n).obj K) ≅
      (DerivedCategory.homologyFunctor
        (ModuleCat (RingedSpace.globalSectionsRing T)) n).obj
          ((RingedSpace.moduleSectionsRestrictionDerived a ⊤).obj K) :=
  exactFunctor_homology_iso_mapDerivedCategory
    (RingedSpace.moduleSectionsRestrictionFunctor a ⊤) K n

/-- A morphism into derived pushforward induces the canonical map on underlying additive
cohomology groups. -/
noncomputable def homologyMapOfPushforward (a : T' ⟶ T)
    {K : DerivedCategory T'.Modules} {L : DerivedCategory T.Modules}
    (α : L ⟶ (RingedSpace.moduleDerivedPushforward a).obj K) (n : ℤ) :
    (forget₂ (ModuleCat (RingedSpace.globalSectionsRing T)) AddCommGrpCat.{u}).obj
        ((DerivedCategory.homologyFunctor
          (ModuleCat (RingedSpace.globalSectionsRing T)) n).obj
            ((RingedSpace.Module.Derived.GlobalSections.functor T).obj L)) ⟶
      (forget₂ (ModuleCat (RingedSpace.globalSectionsRing T')) AddCommGrpCat.{u}).obj
        ((DerivedCategory.homologyFunctor
          (ModuleCat (RingedSpace.globalSectionsRing T')) n).obj
            ((RingedSpace.Module.Derived.GlobalSections.functor T').obj K)) :=
  AddCommGrpCat.ofHom
    (((DerivedCategory.homologyFunctor
          (ModuleCat (RingedSpace.globalSectionsRing T)) n).map
        (RingedSpace.Module.Derived.GlobalSections.mapOfPushforward a α) ≫
      (restrictionHomologyIso a
        ((RingedSpace.Module.Derived.GlobalSections.functor T').obj K) n).inv).hom.toAddMonoidHom)

end AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections
