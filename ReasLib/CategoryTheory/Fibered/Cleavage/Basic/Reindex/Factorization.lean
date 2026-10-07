module

public import ReasLib.CategoryTheory.Fibered.Cleavage.Basic.Reindex.Lift
public import ReasLib.CategoryTheory.Fibered.StronglyCartesian.Ext
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Factorization through chosen cartesian arrows

This leaf owns the universal factor through a cleavage's chosen cartesian arrow and its
specialization to the vertical-cartesian factorization of an arbitrary total-category morphism.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]

open Functor Fiber

namespace Functor.Cleavage

variable {p : S ⥤ C}

/-- The canonical factor of an ambient morphism through the cartesian arrow selected by a
cleavage. The input morphism lies over `g ≫ f`, and the factor lies over `g`. -/
noncomputable def cartesianFactor (chi : p.Cleavage)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) (x : Fiber p U)
    {y : S} (phi : y ⟶ x.1) [p.IsHomLift (g ≫ f) phi] :
    y ⟶ (chi.reindexObj f x).1 :=
  -- Keep this data owner on the cleavage witness itself; the public instance is proof-deferred.
  letI : p.IsStronglyCartesian f (chi.cartesianHom f x) :=
    (chi.reindexLift f x).isStronglyCartesian
  IsStronglyCartesian.map (g := g) (f' := g ≫ f) p f (chi.cartesianHom f x) rfl phi

/-- The canonical factor through a selected cartesian arrow lies over the remaining base arrow. -/
instance cartesianFactor.isHomLift (chi : p.Cleavage)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) (x : Fiber p U)
    {y : S} (phi : y ⟶ x.1) [p.IsHomLift (g ≫ f) phi] :
    p.IsHomLift g (chi.cartesianFactor f g x phi) := sorry

/-- The canonical factor through a selected cartesian arrow has the prescribed composite. -/
@[simp, reassoc]
theorem cartesianFactor.fac (chi : p.Cleavage)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) (x : Fiber p U)
    {y : S} (phi : y ⟶ x.1) [p.IsHomLift (g ≫ f) phi] :
    chi.cartesianFactor f g x phi ≫ chi.cartesianHom f x = phi := sorry

/-- A factor with the correct base arrow and composite is the canonical factor through the
selected cartesian arrow. -/
theorem cartesianFactor.unique (chi : p.Cleavage)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) (x : Fiber p U)
    {y : S} (phi : y ⟶ x.1) [p.IsHomLift (g ≫ f) phi]
    (psi : y ⟶ (chi.reindexObj f x).1) [p.IsHomLift g psi]
    (hpsi : psi ≫ chi.cartesianHom f x = phi) :
    psi = chi.cartesianFactor f g x phi := sorry

/-- The selected cartesian arrow is right-cancellative among ambient arrows lying over the same
base arrow. -/
theorem cartesianHom.hom_ext (chi : p.Cleavage)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) (x : Fiber p U)
    {y : S} {phi psi : y ⟶ (chi.reindexObj f x).1}
    [p.IsHomLift g phi] [p.IsHomLift g psi]
    (h : phi ≫ chi.cartesianHom f x = psi ≫ chi.cartesianHom f x) :
    phi = psi := sorry

/-- Universal-property form of `cartesianFactor`: factors through the selected cartesian arrow
exist uniquely among arrows over the prescribed remaining base arrow. -/
theorem cartesianFactor.existsUnique (chi : p.Cleavage)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) (x : Fiber p U)
    {y : S} (phi : y ⟶ x.1) [p.IsHomLift (g ≫ f) phi] :
    ∃! psi : y ⟶ (chi.reindexObj f x).1,
      p.IsHomLift g psi ∧ psi ≫ chi.cartesianHom f x = phi := sorry

/-- The reindexing target attached to an ambient morphism: the codomain is reindexed along
its image in the base. This is the data owner for vertical-cartesian factorizations. -/
@[stacks 02XN]
def reindexTarget (chi : p.Cleavage) {x y : S} (phi : x ⟶ y) : Fiber p (p.obj x) :=
  chi.reindexObj (p.map phi)
    (Fiber.mk (p := p) (a := y) rfl : Fiber p (p.obj y))

/-- The ambient vertical factor of a morphism through the cartesian arrow selected by a
cleavage. -/
noncomputable def verticalFactorHom (chi : p.Cleavage) {x y : S} (phi : x ⟶ y) :
    x ⟶ (chi.reindexTarget phi).1 :=
  @cartesianFactor C _ S _ p chi (p.obj y) (p.obj x) (p.obj x)
    (p.map phi) (𝟙 (p.obj x))
    (Fiber.mk (p := p) (a := y) rfl : Fiber p (p.obj y)) x phi
    (IsHomLift.lift_id_comp p (p.map phi) phi)

/-- The ambient vertical factor lies over the identity of the source base object. -/
instance verticalFactorHom.isHomLift (chi : p.Cleavage) {x y : S} (phi : x ⟶ y) :
    p.IsHomLift (𝟙 (p.obj x)) (chi.verticalFactorHom phi) := sorry

/-- The vertical factor of an ambient morphism, bundled in the source fiber. -/
@[stacks 02XN]
noncomputable def verticalFactor (chi : p.Cleavage) {x y : S} (phi : x ⟶ y) :
    (Fiber.mk (p := p) (a := x) rfl : Fiber p (p.obj x)) ⟶ chi.reindexTarget phi :=
  ⟨chi.verticalFactorHom phi, verticalFactorHom.isHomLift chi phi⟩

/-- The underlying total-category arrow of the bundled vertical factor is `verticalFactorHom`. -/
@[simp]
theorem verticalFactor.val (chi : p.Cleavage) {x y : S} (phi : x ⟶ y) :
    (chi.verticalFactor phi).1 = chi.verticalFactorHom phi := sorry

/-- The vertical factor followed by the selected cartesian arrow is the original ambient
morphism. -/
@[simp, reassoc, stacks 02XN]
theorem verticalFactor.fac (chi : p.Cleavage) {x y : S} (phi : x ⟶ y) :
    (chi.verticalFactor phi).1 ≫
        chi.cartesianHom (p.map phi)
          (Fiber.mk (p := p) (a := y) rfl : Fiber p (p.obj y)) =
      phi := sorry

/-- A vertical morphism with the prescribed cartesian factorization is the canonical vertical
factor. -/
theorem verticalFactor.unique (chi : p.Cleavage) {x y : S} (phi : x ⟶ y)
    (psi : (Fiber.mk (p := p) (a := x) rfl : Fiber p (p.obj x)) ⟶
      chi.reindexTarget phi)
    (hpsi : psi.1 ≫ chi.cartesianHom (p.map phi)
      (Fiber.mk (p := p) (a := y) rfl : Fiber p (p.obj y)) = phi) :
    psi = chi.verticalFactor phi := sorry

/-- Universal-property form of the bundled vertical factorization. -/
theorem verticalFactor.existsUnique (chi : p.Cleavage) {x y : S} (phi : x ⟶ y) :
    ∃! psi : (Fiber.mk (p := p) (a := x) rfl : Fiber p (p.obj x)) ⟶
        chi.reindexTarget phi,
      psi.1 ≫ chi.cartesianHom (p.map phi)
        (Fiber.mk (p := p) (a := y) rfl : Fiber p (p.obj y)) = phi := sorry

/-- If an ambient morphism is strongly cartesian over its image in the base, its vertical
factor is an isomorphism in the source fiber. -/
theorem verticalFactor.isIso_of_isStronglyCartesian
    (chi : p.Cleavage) {x y : S} (phi : x ⟶ y)
    [p.IsStronglyCartesian (p.map phi) phi] :
    IsIso (chi.verticalFactor phi) := sorry

/-- An ambient morphism whose vertical factor is invertible is strongly cartesian over its
image in the base. -/
theorem verticalFactor.isStronglyCartesian_of_isIso
    (chi : p.Cleavage) {x y : S} (phi : x ⟶ y)
    [IsIso (chi.verticalFactor phi)] :
    p.IsStronglyCartesian (p.map phi) phi := sorry

/-- Strong cartesianness over the image in the base is detected by the vertical factor. -/
theorem verticalFactor.isIso_iff_isStronglyCartesian
    (chi : p.Cleavage) {x y : S} (phi : x ⟶ y) :
    IsIso (chi.verticalFactor phi) ↔ p.IsStronglyCartesian (p.map phi) phi := sorry

/-- Morphisms into a chosen reindexing object are determined by their composites with the chosen
strongly cartesian arrow. -/
theorem cartesianHom.ext (chi : p.Cleavage) {U V : C} (f : V ⟶ U)
    {x : Fiber p U} {y : Fiber p V} {phi psi : y ⟶ chi.reindexObj f x}
    (h : phi.1 ≫ chi.cartesianHom f x = psi.1 ≫ chi.cartesianHom f x) :
    phi = psi := sorry

/-- Composing the chosen cartesian arrow with a morphism in the target fiber remains a lift of
the original base arrow. -/
instance cartesianHom.comp.isHomLift (chi : p.Cleavage) {U V : C} (f : V ⟶ U)
    {x y : Fiber p U} (phi : x ⟶ y) :
    p.IsHomLift f (chi.cartesianHom f x ≫ phi.1) := sorry

end Functor.Cleavage

end CategoryTheory
