module

public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Universe-polymorphic free modules

This leaf provides the free-forget adjunction when the ring and the module
carrier live in independent universes. The object and map data are explicit
finitely supported functions; only functoriality and adjunction laws are
deferred proof obligations.

@stack 01D9
-/

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory.ModuleCat.Free

variable (R : Type u) [Ring R]

/-- The free `R`-module on a type in the common universe containing both the
ring and the generators. -/
@[stacks 01D9 "universe-polymorphic free-module object"]
abbrev obj (X : Type (max u v)) : ModuleCat.{max u v} R :=
  ModuleCat.of R (X →₀ R)

/-- The map of free modules induced by a map of generators. -/
@[stacks 01D9 "free-module map on generators"]
def map {X Y : Type (max u v)} (f : X ⟶ Y) : obj R X ⟶ obj R Y :=
  ModuleCat.ofHom (Finsupp.lmapDomain R R f)

/-- Free-module maps preserve identity maps. -/
@[simp]
theorem map_id (X : Type (max u v)) :
    map R (𝟙 X) = 𝟙 (obj R X) := sorry
/- Proof strategy: apply `ModuleCat.hom_ext` and evaluate the two
`Finsupp.lmapDomain` maps pointwise. -/

/-- Free-module maps preserve composition. -/
theorem map_comp {X Y Z : Type (max u v)} (f : X ⟶ Y) (g : Y ⟶ Z) :
    map R (f ≫ g) = map R f ≫ map R g := sorry
/- Proof strategy: apply `ModuleCat.hom_ext` and use functoriality of
`Finsupp.lmapDomain`. -/

/-- The universe-polymorphic free-module functor. -/
@[stacks 01D9 "universe-polymorphic free-module functor"]
def functor : Type (max u v) ⥤ ModuleCat.{max u v} R where
  obj := obj R
  map := map R
  map_id := map_id R
  map_comp := map_comp R

/-- The canonical free generator associated to `x`. -/
@[stacks 01D9 "canonical free-module generator"]
def mk {X : Type (max u v)} (x : X) : (functor R).obj X :=
  Finsupp.single x 1

/-- The functorial map of free modules sends generators to generators. -/
@[simp]
theorem map_mk {X Y : Type (max u v)} (f : X ⟶ Y) (x : X) :
    (functor R).map f (mk R x) = mk R (f x) := sorry
/- Proof strategy: unfold `functor`, `map`, and `mk`, then use
`Finsupp.mapDomain_single`. -/

/-- The linear map from a free module determined by the images of its
generators. -/
@[stacks 01D9 "free-module descent from generators"]
def desc {X : Type (max u v)} {M : ModuleCat.{max u v} R}
    (f : X ⟶ M) : (functor R).obj X ⟶ M :=
  ModuleCat.ofHom (Finsupp.lift M R X f)

/-- A descended map takes each free generator to its prescribed image. -/
@[simp]
theorem desc_mk {X : Type (max u v)} {M : ModuleCat.{max u v} R}
    (f : X ⟶ M) (x : X) : desc R f (mk R x) = f x := sorry
/- Proof strategy: unfold `desc` and `mk`, then use `Finsupp.lift_apply` and
`Finsupp.sum_single_index`. -/

/-- Linear maps out of a free module are determined by the free
generators. -/
theorem hom_ext {X : Type (max u v)} {M : ModuleCat.{max u v} R}
    {f g : (functor R).obj X ⟶ M}
    (h : ∀ x, f (mk R x) = g (mk R x)) : f = g := sorry
/- Proof strategy: apply `ModuleCat.hom_ext` followed by
`Finsupp.lhom_ext'`, using `h` on each generator. -/

/-- Restrict a linear map from a free module to its generators. -/
@[stacks 01D9 "restriction to free generators"]
def toGenerators {X : Type (max u v)} {M : ModuleCat.{max u v} R}
    (f : (functor R).obj X ⟶ M) : X ⟶ M :=
  ↾(fun x ↦ f (mk R x))

/-- Descending and then restricting to generators recovers the original
linear map. -/
theorem desc_toGenerators {X : Type (max u v)} {M : ModuleCat.{max u v} R}
    (f : (functor R).obj X ⟶ M) :
    desc R (toGenerators R f) = f := sorry
/- Proof strategy: apply `hom_ext` and `desc_mk`. -/

/-- Restricting a descended map to generators recovers the original
function. -/
theorem toGenerators_desc {X : Type (max u v)} {M : ModuleCat.{max u v} R}
    (f : X ⟶ M) : toGenerators R (desc R f) = f := sorry
/- Proof strategy: use function extensionality and `desc_mk`. -/

/-- The universal-property equivalence for a free module. -/
@[stacks 01D9 "free-module universal-property equivalence"]
def homEquiv {X : Type (max u v)} {M : ModuleCat.{max u v} R} :
    ((functor R).obj X ⟶ M) ≃ (X ⟶ M) where
  toFun := toGenerators R
  invFun := desc R
  left_inv := desc_toGenerators R
  right_inv := toGenerators_desc R

/-- The inverse universal-property map is natural in the generators. -/
theorem homEquiv_naturality_left_symm
    {X Y : Type (max u v)} {M : ModuleCat.{max u v} R}
    (f : X ⟶ Y) (g : Y ⟶ M) :
    (homEquiv R).symm (f ≫ g) = (functor R).map f ≫ (homEquiv R).symm g := sorry
/- Proof strategy: apply `hom_ext` and evaluate both sides with `desc_mk`
and `map_mk`. -/

/-- The universal-property equivalence is natural in the target module. -/
theorem homEquiv_naturality_right
    {X : Type (max u v)} {M N : ModuleCat.{max u v} R}
    (f : (functor R).obj X ⟶ M) (g : M ⟶ N) :
    homEquiv R (f ≫ g) =
      homEquiv R f ≫ (CategoryTheory.forget (ModuleCat.{max u v} R)).map g := sorry
/- Proof strategy: use function extensionality and evaluate both sides on a
free generator. -/

/-- The free-module functor is left adjoint to the forgetful functor in the
common universe. -/
@[stacks 01D9 "universe-polymorphic free-forget adjunction"]
def adjunction :
    functor R ⊣ CategoryTheory.forget (ModuleCat.{max u v} R) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ ↦ homEquiv R
      homEquiv_naturality_left_symm := fun {X Y M} f g ↦
        homEquiv_naturality_left_symm R (X := X) (Y := Y) (M := M) f g
      homEquiv_naturality_right := fun {X M N} f g ↦
        homEquiv_naturality_right R (X := X) (M := M) (N := N) f g }

/-- The counit evaluates the free module on the underlying set of a module. -/
@[stacks 01D9 "universe-polymorphic free-module counit"]
abbrev counit :
    CategoryTheory.forget (ModuleCat.{max u v} R) ⋙ functor R ⟶
      𝟭 (ModuleCat.{max u v} R) :=
  (adjunction R).counit

/-- The free-forget counit sends each free generator to the element that
labels it. -/
@[simp]
theorem counit_mk (M : ModuleCat.{max u v} R) (m : M) :
    (counit R).app M (mk R m) = m := sorry
/- Proof strategy: unfold `counit` and `adjunction`, then identify the
adjunction counit with `desc R (𝟙 M)` and apply `desc_mk`. -/

/-- Every free-forget counit component is an epimorphism. -/
@[stacks 01D9 "free-module counit is epic"]
instance counit_app_epi (M : ModuleCat.{max u v} R) :
    Epi ((counit R).app M) := sorry
/- Proof strategy: use `ModuleCat.epi_iff_surjective`; every `m : M` is the
image of the free generator `mk R m` by `counit_mk`. -/

end CategoryTheory.ModuleCat.Free
