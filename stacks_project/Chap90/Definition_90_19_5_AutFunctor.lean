module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.FiberedCategory.Cocartesian
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Types.Basic
public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Basic.Coherence
public import ReasLib.CategoryTheory.Fibered.Fiber.Isomorphism
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic

/-!
# Automorphism functors of cofibered-in-groupoids objects

For `p : F ⥤ C` cofibered in groupoids, a choice of pushforwards is the selected
cleavage of `p.op`. The automorphism functor of `x : F` is the covariant
`Type`-valued functor on `Under (p.obj x)` sending `f` to the automorphism group
of the selected pushforward `f_* x` in the fibre over the codomain of `f`.
-/

@[expose] public section

open CategoryTheory Opposite Under

universe u₁ v₁ u₂ v₂

variable {C : Type u₁} [Category.{v₁} C]
variable {F : Type u₂} [Category.{v₂} F]

namespace CategoryTheory.Functor.Fiber

/-- The standard fibre object determined by an object of the total category. -/
def ofObj (p : F ⥤ C) (x : F) : p.Fiber (p.obj x) := ⟨x, rfl⟩

/-- The underlying total-category object of `ofObj p x` is `x`. -/
theorem ofObj_coe (p : F ⥤ C) (x : F) : (ofObj p x).1 = x := sorry

/-- The object of `p.op.Fiber (op U)` corresponding to an object of `p.Fiber U`. -/
def toOp {p : F ⥤ C} {U : C} (x : p.Fiber U) : p.op.Fiber (op U) :=
  ⟨op x.1, congrArg op x.2⟩

/-- The object of `p.Fiber U` corresponding to an object of `p.op.Fiber (op U)`. -/
def fromOp {p : F ⥤ C} {U : C} (x : p.op.Fiber (op U)) : p.Fiber U :=
  ⟨x.1.unop, Opposite.op_injective x.2⟩

/-- Converting a fibre object to the opposite fibre and back recovers the object. -/
theorem fromOp_toOp {p : F ⥤ C} {U : C} (x : p.Fiber U) : fromOp (toOp x) = x := sorry

/-- Converting an opposite fibre object to the original fibre and back recovers the object. -/
theorem toOp_fromOp {p : F ⥤ C} {U : C} (x : p.op.Fiber (op U)) : toOp (fromOp x) = x := sorry

/-- The identity comparison `toOp (fromOp y) ≅ y` on the common total-category object. -/
def toOpFromOpIso {p : F ⥤ C} {U : C} (y : p.op.Fiber (op U)) : toOp (fromOp y) ≅ y :=
  isoMk (Iso.refl y.1) (IsHomLift.id y.2)

/-- The identity comparison `fromOp (toOp x) ≅ x` on the common total-category object. -/
def fromOpToOpIso {p : F ⥤ C} {U : C} (x : p.Fiber U) : fromOp (toOp x) ≅ x :=
  isoMk (Iso.refl x.1) (IsHomLift.id x.2)

/-- The forward map of `toOpFromOpIso` is the identity on the underlying total-category object. -/
theorem toOpFromOpIso_hom {p : F ⥤ C} {U : C} (y : p.op.Fiber (op U)) :
    (toOpFromOpIso y).hom.1 = 𝟙 y.1 := sorry

/-- The forward map of `fromOpToOpIso` is the identity on the underlying total-category object. -/
theorem fromOpToOpIso_hom {p : F ⥤ C} {U : C} (x : p.Fiber U) :
    (fromOpToOpIso x).hom.1 = 𝟙 x.1 := sorry

/-- Opposite of a fibre automorphism, as an automorphism of the opposite fibre object. -/
def toOpAut {p : F ⥤ C} {U : C} {x : p.Fiber U} (α : Aut x) : Aut (toOp x) :=
  isoMk (Iso.op (fiberInclusion.mapIso α)) sorry

/-- Unopposite of an opposite-fibre automorphism, as an automorphism of the original fibre. -/
def fromOpAut {p : F ⥤ C} {U : C} {y : p.op.Fiber (op U)} (α : Aut y) : Aut (fromOp y) :=
  isoMk (Iso.unop (fiberInclusion.mapIso α)) sorry

/-- The underlying total arrow of `toOpAut α` is the opposite of the underlying arrow of `α`. -/
theorem toOpAut_hom {p : F ⥤ C} {U : C} {x : p.Fiber U} (α : Aut x) :
    (toOpAut α).hom.1 = α.hom.1.op := sorry

/-- The underlying total arrow of `fromOpAut α` is the unopposite of the underlying arrow of `α`. -/
theorem fromOpAut_hom {p : F ⥤ C} {U : C} {y : p.op.Fiber (op U)} (α : Aut y) :
    (fromOpAut α).hom.1 = α.hom.1.unop := sorry

end CategoryTheory.Functor.Fiber

namespace CategoryTheory.Functor.Chosen

open Fiber

/-- The selected pushforward of a fibre object along a base arrow, obtained from the chosen
cleavage of `p.op`. -/
noncomputable def pushforwardObj (p : F ⥤ C) [p.op.IsFibered] {U V : C} (f : U ⟶ V)
    (x : p.Fiber U) : p.Fiber V :=
  fromOp (reindexObj p.op f.op (toOp x))

/-- The selected pushforward lies in the fibre over the codomain of its base arrow. -/
theorem pushforwardObj_property (p : F ⥤ C) [p.op.IsFibered] {U V : C} (f : U ⟶ V)
    (x : p.Fiber U) :
    p.obj (pushforwardObj p f x).1 = V := sorry

/-- The selected pushforward object is the unopposite of the chosen reindexing of `p.op`. -/
theorem pushforwardObj_eq_fromOp (p : F ⥤ C) [p.op.IsFibered] {U V : C} (f : U ⟶ V)
    (x : p.Fiber U) :
    pushforwardObj p f x = fromOp (reindexObj p.op f.op (toOp x)) := sorry

/-- The selected cocartesian lift `x ⟶ f_* x`, as the unopposite of the chosen cartesian arrow
of `p.op`. -/
noncomputable def pushforwardHom (p : F ⥤ C) [p.op.IsFibered] {U V : C} (f : U ⟶ V)
    (x : p.Fiber U) : x.1 ⟶ (pushforwardObj p f x).1 :=
  (cartesianHom p.op f.op (toOp x)).unop

/-- The selected pushforward arrow is strongly cocartesian over its base arrow. -/
instance pushforwardHom.isStronglyCocartesian (p : F ⥤ C) [p.op.IsFibered]
    {U V : C} (f : U ⟶ V) (x : p.Fiber U) :
    p.IsStronglyCocartesian f (pushforwardHom p f x) := sorry

/-- The selected pushforward arrow lies over its displayed base arrow. -/
theorem pushforwardHom_isHomLift (p : F ⥤ C) [p.op.IsFibered] {U V : C} (f : U ⟶ V)
    (x : p.Fiber U) :
    p.IsHomLift f (pushforwardHom p f x) := sorry

/-- The selected comparison isomorphism in the opposite fibre for a specified composite
`f.hom ≫ φ.right = g.hom`. -/
noncomputable def pushforwardCompIso (p : F ⥤ C) [p.op.IsFibered] {U : C}
    {f g : Under U} (φ : f ⟶ g) (x : p.Fiber U) :
    reindexObj p.op g.hom.op (toOp x) ≅
      reindexObj p.op φ.right.op (reindexObj p.op f.hom.op (toOp x)) :=
  Reindex.specifiedCompIsoApp p.op f.hom.op φ.right.op g.hom.op
    (op_comp.symm.trans (congrArg Quiver.Hom.op (Under.w φ))) (toOp x)

/-- The selected comparison isomorphism is the specified-composite comparison of `p.op`. -/
theorem pushforwardCompIso_eq_specifiedCompIsoApp (p : F ⥤ C) [p.op.IsFibered] {U : C}
    {f g : Under U} (φ : f ⟶ g) (x : p.Fiber U) :
    pushforwardCompIso p φ x =
      Reindex.specifiedCompIsoApp p.op f.hom.op φ.right.op g.hom.op
        (op_comp.symm.trans (congrArg Quiver.Hom.op (Under.w φ))) (toOp x) := sorry

/-- The unique comparison `f_* x ⟶ g_* x` over an under-morphism `φ`, compatible with the two
selected pushforward arrows from `x`. -/
noncomputable def pushforwardComparison (p : F ⥤ C) [p.op.IsFibered] {U : C}
    {f g : Under U} (φ : f ⟶ g) (x : p.Fiber U) :
    (pushforwardObj p f.hom x).1 ⟶ (pushforwardObj p g.hom x).1 :=
  ((pushforwardCompIso p φ x).hom.1 ≫
      cartesianHom p.op φ.right.op (reindexObj p.op f.hom.op (toOp x))).unop

/-- The selected comparison arrow lies over the under-morphism's base arrow. -/
theorem pushforwardComparison_isHomLift (p : F ⥤ C) [p.op.IsFibered] {U : C}
    {f g : Under U} (φ : f ⟶ g) (x : p.Fiber U) :
    p.IsHomLift φ.right (pushforwardComparison p φ x) := sorry

/-- The selected comparison arrow is compatible with the two pushforward arrows from `x`. -/
theorem pushforwardComparison_fac (p : F ⥤ C) [p.op.IsFibered] {U : C}
    {f g : Under U} (φ : f ⟶ g) (x : p.Fiber U) :
    pushforwardHom p f.hom x ≫ pushforwardComparison p φ x =
      pushforwardHom p g.hom x := sorry

/-- A comparison over `φ.right` compatible with the two selected pushforward arrows is the
selected comparison. -/
theorem pushforwardComparison_unique (p : F ⥤ C) [p.op.IsFibered] {U : C}
    {f g : Under U} (φ : f ⟶ g) (x : p.Fiber U)
    (ψ : (pushforwardObj p f.hom x).1 ⟶ (pushforwardObj p g.hom x).1)
    (hψ : p.IsHomLift φ.right ψ)
    (hfac : pushforwardHom p f.hom x ≫ ψ = pushforwardHom p g.hom x) :
    ψ = pushforwardComparison p φ x := sorry

/-- The homomorphism `Aut(f_* x) → Aut(g_* x)` induced by the selected comparison of an
under-morphism. -/
noncomputable def pushforwardAut (p : F ⥤ C) [p.op.IsFibered] {U : C}
    {f g : Under U} (φ : f ⟶ g) (x : p.Fiber U) :
    Aut (pushforwardObj p f.hom x) → Aut (pushforwardObj p g.hom x) :=
  fun α ↦
    let yf := reindexObj p.op f.hom.op (toOp x)
    let αop := Aut.autMulEquivOfIso (toOpFromOpIso yf) (toOpAut α)
    let αreindex := mapAut yf (reindex p.op φ.right.op) αop
    fromOpAut ((Aut.autMulEquivOfIso (pushforwardCompIso p φ x)).symm αreindex)

/-- The selected comparison conjugates a fibre automorphism to its pushforward. -/
theorem pushforwardAut_fac (p : F ⥤ C) [p.op.IsFibered] {U : C} {f g : Under U}
    (φ : f ⟶ g) (x : p.Fiber U) (α : Aut (pushforwardObj p f.hom x)) :
    pushforwardComparison p φ x ≫ (pushforwardAut p φ x α).hom.1 =
      α.hom.1 ≫ pushforwardComparison p φ x := sorry

/-- Pushforward of fibre automorphisms preserves multiplication. -/
theorem pushforwardAut_mul (p : F ⥤ C) [p.op.IsFibered] {U : C} {f g : Under U}
    (φ : f ⟶ g) (x : p.Fiber U) (α β : Aut (pushforwardObj p f.hom x)) :
    pushforwardAut p φ x (α * β) = pushforwardAut p φ x α * pushforwardAut p φ x β := sorry

/-- Pushforward of fibre automorphisms preserves the identity. -/
theorem pushforwardAut_one (p : F ⥤ C) [p.op.IsFibered] {U : C} {f g : Under U}
    (φ : f ⟶ g) (x : p.Fiber U) :
    pushforwardAut p φ x 1 = 1 := sorry

end CategoryTheory.Functor.Chosen

namespace CategoryTheory.Functor

open Fiber Chosen

/-- The automorphism functor of an object of a category cofibered in groupoids. -/
noncomputable def autFunctor (p : F ⥤ C) [IsFibered.InGroupoids p.op] (x : F) :
    Under (p.obj x) ⥤ Type v₂ where
  obj f := Aut (pushforwardObj p f.hom (ofObj p x))
  map φ := TypeCat.ofHom (pushforwardAut p φ (ofObj p x))
  map_id := sorry
  map_comp := sorry

/-- On objects, the automorphism functor evaluates to automorphisms of the selected
pushforward in the fibre over the codomain. -/
theorem autFunctor_obj (p : F ⥤ C) [IsFibered.InGroupoids p.op] (x : F)
    (f : Under (p.obj x)) :
    (autFunctor p x).obj f = Aut (pushforwardObj p f.hom (ofObj p x)) := sorry

/-- On morphisms, the automorphism functor acts by the selected-comparison homomorphism. -/
theorem autFunctor_map (p : F ⥤ C) [IsFibered.InGroupoids p.op] (x : F)
    {f g : Under (p.obj x)} (φ : f ⟶ g) :
    (autFunctor p x).map φ = TypeCat.ofHom (pushforwardAut p φ (ofObj p x)) := sorry

/-- The comparison of an under-morphism conjugates fibre automorphisms to their images. -/
theorem autFunctor_map_fac (p : F ⥤ C) [IsFibered.InGroupoids p.op] (x : F)
    {f g : Under (p.obj x)} (φ : f ⟶ g)
    (α : Aut (pushforwardObj p f.hom (ofObj p x))) :
    pushforwardComparison p φ (ofObj p x) ≫ ((autFunctor p x).map φ α).hom.1 =
      α.hom.1 ≫ pushforwardComparison p φ (ofObj p x) := sorry

/-- The image of an under-morphism under the automorphism functor is a group homomorphism. -/
theorem autFunctor.map_mul (p : F ⥤ C) [IsFibered.InGroupoids p.op] (x : F)
    {f g : Under (p.obj x)} (φ : f ⟶ g)
    (α β : Aut (pushforwardObj p f.hom (ofObj p x))) :
    pushforwardAut p φ (ofObj p x) (α * β) =
      pushforwardAut p φ (ofObj p x) α * pushforwardAut p φ (ofObj p x) β := sorry

/-- The automorphism functor sends every under-morphism to a unital map on fibre automorphisms. -/
theorem autFunctor.map_one (p : F ⥤ C) [IsFibered.InGroupoids p.op] (x : F)
    {f g : Under (p.obj x)} (φ : f ⟶ g) :
    pushforwardAut p φ (ofObj p x) 1 = 1 := sorry

end CategoryTheory.Functor

