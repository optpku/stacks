module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pushforward.Additive
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Grothendieck
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Flasque
import Mathlib.Tactic.CrossRefAttribute

/-!
# Higher Direct Images of Modules on Ringed Spaces

This file owns the classical higher direct images of module sheaves along a morphism of ringed
spaces. The object and map API is functorial by construction; the injective-resolution
comparison provides its standard computational model.
-/

@[expose] public section

open AlgebraicGeometry.RingedSpace.Hom

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Hom

/-- The degree-`i` higher direct image functor on module sheaves along a morphism of ringed
spaces. -/
abbrev higherDirectImageModuleFunctor
    {X Y : RingedSpace.{u}} (f : X ⟶ Y) (i : ℕ) : X.Modules ⥤ Y.Modules :=
  (pushforward f).rightDerived i

/-- The degree-`i` higher direct image of a module sheaf along a morphism of ringed spaces. -/
@[stacks 0715 "ringed-space higher direct image"]
abbrev higherDirectImageModule
    {X Y : RingedSpace.{u}} (f : X ⟶ Y) (F : X.Modules) (i : ℕ) : Y.Modules :=
  (higherDirectImageModuleFunctor f i).obj F

/-- The map on higher direct images induced by a morphism of module sheaves. -/
abbrev higherDirectImageModuleMap
    {X Y : RingedSpace.{u}} (f : X ⟶ Y) {F G : X.Modules} (a : F ⟶ G) (i : ℕ) :
    higherDirectImageModule f F i ⟶ higherDirectImageModule f G i :=
  (higherDirectImageModuleFunctor f i).map a

namespace HigherDirectImage

/-- Vanishing of all positive higher direct images is the ordinary right-derived vanishing
condition for module pushforward. -/
@[stacks 0715 "positive ringed-space higher direct-image vanishing"]
theorem vanishesAboveZero_iff
    {X Y : RingedSpace.{u}} (f : X ⟶ Y) (F : X.Modules) :
    (∀ n : ℕ, IsZero (((pushforward f).rightDerived (n + 1)).obj F)) ↔
      ∀ i : ℕ, 0 < i → IsZero (higherDirectImageModule f F i) := sorry

/-- Positive higher direct images along the identity morphism vanish. -/
@[stacks 03BA "identity higher direct image vanishing"]
theorem isZero_identity_of_pos
    (X : RingedSpace.{u}) (F : X.Modules) {i : ℕ} (hi : 0 < i) :
    IsZero (higherDirectImageModule (𝟙 X) F i) := sorry

/-- Positive higher direct images of a flasque module sheaf vanish. -/
@[stacks 09T0 "positive higher direct images of flasque modules vanish"]
theorem isZero_of_flasque
    {X Y : RingedSpace.{u}} (f : X ⟶ Y) {F : X.Modules}
    (hF : Modules.flasque X F) {i : ℕ} (hi : 0 < i) :
    IsZero (higherDirectImageModule f F i) := sorry

/-- A chosen injective resolution computes the higher direct image through the homology of its
pushforward. -/
@[stacks 0715 "injective-resolution computation"]
noncomputable abbrev isoHomologyPushforward
    {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    (F : X.Modules) (I : InjectiveResolution F) (i : ℕ) :
    higherDirectImageModule f F i ≅
      (HomologicalComplex.homologyFunctor Y.Modules (ComplexShape.up ℕ) i).obj
        (((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex) :=
  I.isoRightDerivedObj (pushforward f) i

end HigherDirectImage

end AlgebraicGeometry.RingedSpace.Hom
