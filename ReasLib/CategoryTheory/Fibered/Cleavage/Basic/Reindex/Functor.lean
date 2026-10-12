/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Cleavage.Basic.Reindex.Factorization
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Reindexing functors from a cleavage

This leaf constructs the action on fiber morphisms from cartesian factorization and packages it
as the reindexing functor. Computation, uniqueness, identity, and composition laws form the public
interface; downstream code should not unfold the chosen factor.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]

open Functor Fiber

namespace Functor.Cleavage

variable {p : S ⥤ C}

set_option backward.privateInPublic true in
/-- The ambient total-category arrow selected by cartesian factorization when reindexing a fiber
morphism. This private owner supplies the non-Prop payload of `reindexMap`. -/
private noncomputable def reindexMapHom (chi : p.Cleavage)
    {U V : C} (f : V ⟶ U) {x y : Fiber p U} (phi : x ⟶ y) :
    (chi.reindexObj f x).1 ⟶ (chi.reindexObj f y).1 :=
  @IsStronglyCartesian.map C S _ _ p V U (chi.reindexObj f y).1 y.1
    f (chi.cartesianHom f y) (chi.reindexLift f y).isStronglyCartesian
    V (chi.reindexObj f x).1 (𝟙 V) f (Category.id_comp f).symm
    (chi.cartesianHom f x ≫ phi.1)
    (@IsHomLift.comp_lift_id_right' C S _ _ p V U
      (chi.reindexObj f x).1 x.1 y.1 f (chi.cartesianHom f x)
      (chi.reindexLift f x).isStronglyCartesian.toIsHomLift U phi.1 phi.2)

set_option backward.privateInPublic true in
/-- The ambient arrow selected by `reindexMapHom` lies over the identity of the source fiber. -/
private theorem reindexMapHom.isHomLift (chi : p.Cleavage)
    {U V : C} (f : V ⟶ U) {x y : Fiber p U} (phi : x ⟶ y) :
    p.IsHomLift (𝟙 V) (reindexMapHom chi f phi) := sorry

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The action on fiber morphisms forced by the chosen strongly cartesian arrows. Its public
characterization is `reindexMap.fac`, with uniqueness supplied by `reindexMap.unique`. -/
noncomputable def reindexMap (chi : p.Cleavage)
    {U V : C} (f : V ⟶ U) {x y : Fiber p U} (phi : x ⟶ y) :
    chi.reindexObj f x ⟶ chi.reindexObj f y :=
  ⟨reindexMapHom chi f phi, reindexMapHom.isHomLift chi f phi⟩

/-- The underlying total-category arrow of a reindexing map lies over the identity. -/
theorem reindexMap.isHomLift (chi : p.Cleavage)
    {U V : C} (f : V ⟶ U) {x y : Fiber p U} (phi : x ⟶ y) :
    p.IsHomLift (𝟙 V) (chi.reindexMap f phi).1 := sorry

/-- Reindexing on morphisms is characterized by factorization through the chosen cartesian
arrow. -/
@[simp, reassoc]
theorem reindexMap.fac (chi : p.Cleavage)
    {U V : C} (f : V ⟶ U) {x y : Fiber p U} (phi : x ⟶ y) :
    (chi.reindexMap f phi).1 ≫ chi.cartesianHom f y =
      chi.cartesianHom f x ≫ phi.1 := sorry

/-- A fiber morphism with the defining cartesian factorization is the chosen reindexing map. -/
theorem reindexMap.unique (chi : p.Cleavage)
    {U V : C} (f : V ⟶ U) {x y : Fiber p U} (phi : x ⟶ y)
    (psi : chi.reindexObj f x ⟶ chi.reindexObj f y)
    (hpsi : psi.1 ≫ chi.cartesianHom f y = chi.cartesianHom f x ≫ phi.1) :
    psi = chi.reindexMap f phi := sorry

/-- Universal-property form of the reindexing map in the source fiber. -/
theorem reindexMap.existsUnique (chi : p.Cleavage)
    {U V : C} (f : V ⟶ U) {x y : Fiber p U} (phi : x ⟶ y) :
    ∃! psi : chi.reindexObj f x ⟶ chi.reindexObj f y,
      psi.1 ≫ chi.cartesianHom f y = chi.cartesianHom f x ≫ phi.1 := sorry

/-- Reindexing sends identity morphisms in a fiber to identity morphisms. -/
@[simp]
theorem reindexMap.id (chi : p.Cleavage)
    {U V : C} (f : V ⟶ U) (x : Fiber p U) :
    chi.reindexMap f (𝟙 x) = 𝟙 (chi.reindexObj f x) := sorry

/-- Reindexing respects composition in each fiber. -/
@[simp]
theorem reindexMap.comp (chi : p.Cleavage)
    {U V : C} (f : V ⟶ U) {x y z : Fiber p U} (phi : x ⟶ y) (psi : y ⟶ z) :
    chi.reindexMap f (phi ≫ psi) = chi.reindexMap f phi ≫ chi.reindexMap f psi := sorry

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The reindexing functor on standard fibers induced by a cleavage. Its actions are exposed by
`reindex.obj`, `reindex.map`, and `reindex.map_fac`. -/
@[stacks 02XN "reindexing functor induced by a pullback choice"]
noncomputable def reindex (chi : p.Cleavage) {U V : C} (f : V ⟶ U) :
    Fiber p U ⥤ Fiber p V where
  obj := chi.reindexObj f
  map := chi.reindexMap f
  map_id := reindexMap.id chi f
  map_comp := reindexMap.comp chi f

/-- The object action of `reindex` is the chosen standard-fiber lift. -/
@[simp]
theorem reindex.obj (chi : p.Cleavage) {U V : C} (f : V ⟶ U) (x : Fiber p U) :
    (chi.reindex f).obj x = chi.reindexObj f x := sorry

/-- The morphism action of `reindex` is the universal factorization `reindexMap`. -/
@[simp]
theorem reindex.map (chi : p.Cleavage) {U V : C} (f : V ⟶ U)
    {x y : Fiber p U} (phi : x ⟶ y) :
    (chi.reindex f).map phi = chi.reindexMap f phi := sorry

/-- The functorial morphism action satisfies the defining cartesian factorization directly. -/
@[simp, reassoc]
theorem reindex.map_fac (chi : p.Cleavage) {U V : C} (f : V ⟶ U)
    {x y : Fiber p U} (phi : x ⟶ y) :
    ((chi.reindex f).map phi).1 ≫ chi.cartesianHom f y =
      chi.cartesianHom f x ≫ phi.1 := sorry

/-- A morphism with the defining factorization is the map of the reindexing functor. -/
theorem reindex.map_unique (chi : p.Cleavage) {U V : C} (f : V ⟶ U)
    {x y : Fiber p U} (phi : x ⟶ y)
    (psi : chi.reindexObj f x ⟶ chi.reindexObj f y)
    (hpsi : psi.1 ≫ chi.cartesianHom f y = chi.cartesianHom f x ≫ phi.1) :
    psi = (chi.reindex f).map phi := sorry

end Functor.Cleavage

end CategoryTheory

/- The standard notation for the reindexing functor along `f`. The explicit cleavage prevents a
noncanonical choice from being hidden at the reusable API boundary. -/
notation:90 f:91 "⁎[" chi "]" =>
  CategoryTheory.Functor.Cleavage.reindex chi f

/- The object form is a separate notation production because at this precedence Lean does not
parse `f⁎[chi] x` as coercion-based application of the functor notation. -/
notation:90 f:91 "⁎[" chi "] " x:90 =>
  CategoryTheory.Functor.Cleavage.reindexObj chi f x
