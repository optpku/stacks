module

public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous.Additive
public import ReasLib.CategoryTheory.Fibered.YonedaEvaluation.Groupoids
public import stacks_project.Chap96.Lemma_96_10_1_Comparison
public import stacks_project.Chap96.Lemma_96_12_3_Pullback

/-!
# Small-étale restriction of étale modules at an object

Restriction of étale `𝒪`-modules to the small étale site of `p(y)`, and coefficient
restriction along a representing algebraic space of a slice 2-fibre product.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.GroupoidsOver FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.HigherDirectImageRestriction

variable {S : Scheme.{u}}

/-- The Yoneda 1-morphism `slice (p(y)) ⟶ Y` associated to an object `y` of `Y`. -/
abbrev sliceHom {Y : GroupoidsOver S} (y : Y.total) :
    GroupoidsOver.slice (Y.p.obj y) ⟶ Y :=
  YonedaSlice.representative (⟨y, rfl⟩ : Y.p.Fiber (Y.p.obj y))

/-- `sliceHom y` is the Yoneda representative of the fibre object `⟨y, rfl⟩`. -/
theorem sliceHom_eq {Y : GroupoidsOver S} (y : Y.total) :
    sliceHom y = YonedaSlice.representative (⟨y, rfl⟩ : Y.p.Fiber (Y.p.obj y)) :=
  rfl

/-- Restriction of étale `𝒪_X`-modules to the small étale site of a representing algebraic
space, along a bicategorical equivalence `e : U.toGroupoids ≌ X`. -/
def restrictAlong {U : AlgebraicSpace S} {X : GroupoidsOver S}
    (e : U.toGroupoids ≌ X) :
    etaleModules X ⥤ AlgebraicSpace.Modules U :=
  (pi U X e).modulePushforward

/-- `restrictAlong e` is module pushforward along `π_U`. -/
theorem restrictAlong_eq {U : AlgebraicSpace S} {X : GroupoidsOver S}
    (e : U.toGroupoids ≌ X) :
    restrictAlong e = (pi U X e).modulePushforward :=
  rfl

/-- Restriction of étale modules on `Y` to the small étale site of the algebraic space
`ofOver (p(y))`. -/
def restrictAt {Y : GroupoidsOver S} (y : Y.total) :
    etaleModules Y ⥤ AlgebraicSpace.Modules (AlgebraicSpace.ofOver (Y.p.obj y)) :=
  moduleInverseImage (sliceHom y) ⋙
    restrictAlong (AlgebraicSpace.ofOverSliceEquiv (Y.p.obj y))

/-- `restrictAt y` is inverse image along `sliceHom y` followed by restriction along
`ofOverSliceEquiv`. -/
theorem restrictAt_eq {Y : GroupoidsOver S} (y : Y.total) :
    restrictAt y =
      moduleInverseImage (sliceHom y) ⋙
        restrictAlong (AlgebraicSpace.ofOverSliceEquiv (Y.p.obj y)) :=
  rfl

/-- The second projection of the slice 2-fibre product of `f` along `sliceHom y`. -/
abbrev snd {X Y : GroupoidsOver S} (f : X ⟶ Y) (y : Y.total) :
    TwoFibreProduct.apex.{u + 1, u, u + 1, u} (sliceHom y) f ⟶ X :=
  TwoFibreProduct.snd.{u + 1, u, u + 1, u} (sliceHom y) f

/-- Coefficient restriction of an étale module on `X` to `U_étale`, by inverse image along
`snd` followed by restriction along a representing equivalence of `V ×_Y X`. -/
def restrictToU {X Y : GroupoidsOver S} (f : X ⟶ Y) (y : Y.total)
    (U : AlgebraicSpace S)
    (eU : U.toGroupoids ≌ TwoFibreProduct.apex.{u + 1, u, u + 1, u} (sliceHom y) f) :
    etaleModules X ⥤ AlgebraicSpace.Modules U :=
  moduleInverseImage (snd f y) ⋙ restrictAlong eU

/-- `restrictToU` is inverse image along `snd` followed by restriction along `eU`. -/
theorem restrictToU_eq {X Y : GroupoidsOver S} (f : X ⟶ Y) (y : Y.total)
    (U : AlgebraicSpace S)
    (eU : U.toGroupoids ≌ TwoFibreProduct.apex.{u + 1, u, u + 1, u} (sliceHom y) f) :
    restrictToU f y U eU = moduleInverseImage (snd f y) ⋙ restrictAlong eU :=
  rfl

/-- `restrictAlong` is additive, as module pushforward along a morphism of ringed sites. -/
instance restrictAlong_additive {U : AlgebraicSpace S} {X : GroupoidsOver S}
    (e : U.toGroupoids ≌ X) : (restrictAlong e).Additive :=
  sorry

/-- Inverse image of étale modules is additive. -/
instance moduleInverseImage_additive {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    (moduleInverseImage f).Additive :=
  sorry

/-- `restrictAt y` is additive. -/
instance restrictAt_additive {Y : GroupoidsOver S} (y : Y.total) :
    (restrictAt y).Additive :=
  sorry

/-- `restrictToU` is additive. -/
instance restrictToU_additive {X Y : GroupoidsOver S} (f : X ⟶ Y) (y : Y.total)
    (U : AlgebraicSpace S)
    (eU : U.toGroupoids ≌ TwoFibreProduct.apex.{u + 1, u, u + 1, u} (sliceHom y) f) :
    (restrictToU f y U eU).Additive :=
  sorry

/-- Restriction to the small étale site of `p(y)` preserves finite limits. -/
instance restrictAt_preservesFiniteLimits {Y : GroupoidsOver S} (y : Y.total) :
    PreservesFiniteLimits (restrictAt y) :=
  sorry

/-- Restriction to the small étale site of `p(y)` preserves finite colimits. -/
instance restrictAt_preservesFiniteColimits {Y : GroupoidsOver S} (y : Y.total) :
    PreservesFiniteColimits (restrictAt y) :=
  sorry

/-- Coefficient restriction to `U_étale` preserves finite limits. -/
instance restrictToU_preservesFiniteLimits {X Y : GroupoidsOver S}
    (f : X ⟶ Y) (y : Y.total) (U : AlgebraicSpace S)
    (eU : U.toGroupoids ≌ TwoFibreProduct.apex.{u + 1, u, u + 1, u} (sliceHom y) f) :
    PreservesFiniteLimits (restrictToU f y U eU) :=
  sorry

/-- Coefficient restriction to `U_étale` preserves finite colimits. -/
instance restrictToU_preservesFiniteColimits {X Y : GroupoidsOver S}
    (f : X ⟶ Y) (y : Y.total) (U : AlgebraicSpace S)
    (eU : U.toGroupoids ≌ TwoFibreProduct.apex.{u + 1, u, u + 1, u} (sliceHom y) f) :
    PreservesFiniteColimits (restrictToU f y U eU) :=
  sorry

end AlgebraicGeometry.GroupoidsOver.HigherDirectImageRestriction
