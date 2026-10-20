module

public import ReasLib.CategoryTheory.Cofibered.Fiber
public import ReasLib.CategoryTheory.Fibered.Cleavage.ReindexIso.Composition
public import ReasLib.CategoryTheory.Fibered.Cleavage.ReindexIso.Transport
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.CatCommSqOver

/-!
# Pushforward comparison along a commuting square

A cleavage of the opposite projection induces composition and equality-transport comparisons
for pushforwards. These give a comparison from the fibre over a commuting square's apex to the
categorical pullback of its two outgoing pushforward functors.
-/

@[expose] public section

open CategoryTheory Limits CategoricalPullback Opposite
open scoped CategoricalPullback

universe u v uF vF

variable {C : Type u} [Category.{v} C]
variable {F : Type uF} [Category.{vF} F]

namespace CategoryTheory.Functor

/-- The forward comparison from successive pushforwards to pushforward along the composite,
including the transport identifying the intermediate opposite-fibre object. -/
noncomputable def pushforwardFiberCompHom (p : F ⥤ C) (χ : p.op.Cleavage)
    {U V W : C} (f : U ⟶ V) (g : V ⟶ W) (x : p.Fiber U) :
    (pushforwardFiberFunctor p χ f ⋙ pushforwardFiberFunctor p χ g).obj x ⟶
      (pushforwardFiberFunctor p χ (f ≫ g)).obj x :=
  let xOp := toOpFiber p x
  let yOp := (χ.reindex f.op).obj xOp
  let hRound : toOpFiber p (fromOpFiber p yOp) = yOp := Subtype.ext rfl
  (eqToIso (congrArg (fun z ↦ fromOpFiber p ((χ.reindex g.op).obj z)) hRound)).hom ≫
    fromOpFiberHom p ((Cleavage.Reindex.compIso χ f.op g.op).hom.app xOp)

/-- The inverse comparison from pushforward along a composite to successive pushforwards,
including the inverse intermediate opposite-fibre transport. -/
noncomputable def pushforwardFiberCompInv (p : F ⥤ C) (χ : p.op.Cleavage)
    {U V W : C} (f : U ⟶ V) (g : V ⟶ W) (x : p.Fiber U) :
    (pushforwardFiberFunctor p χ (f ≫ g)).obj x ⟶
      (pushforwardFiberFunctor p χ f ⋙ pushforwardFiberFunctor p χ g).obj x :=
  let xOp := toOpFiber p x
  let yOp := (χ.reindex f.op).obj xOp
  let hRound : toOpFiber p (fromOpFiber p yOp) = yOp := Subtype.ext rfl
  fromOpFiberHom p ((Cleavage.Reindex.compIso χ f.op g.op).inv.app xOp) ≫
    (eqToIso (congrArg (fun z ↦ fromOpFiber p ((χ.reindex g.op).obj z)) hRound)).inv

/-- The forward composition comparison followed by its inverse is the identity on the
successive pushforward. -/
theorem pushforwardFiberCompHom_inv_id (p : F ⥤ C) (χ : p.op.Cleavage)
    {U V W : C} (f : U ⟶ V) (g : V ⟶ W) (x : p.Fiber U) :
    pushforwardFiberCompHom p χ f g x ≫ pushforwardFiberCompInv p χ f g x =
      𝟙 ((pushforwardFiberFunctor p χ f ⋙ pushforwardFiberFunctor p χ g).obj x) := sorry

/-- The inverse composition comparison followed by the forward comparison is the identity
on the pushforward along the composite. -/
theorem pushforwardFiberCompInv_hom_id (p : F ⥤ C) (χ : p.op.Cleavage)
    {U V W : C} (f : U ⟶ V) (g : V ⟶ W) (x : p.Fiber U) :
    pushforwardFiberCompInv p χ f g x ≫ pushforwardFiberCompHom p χ f g x =
      𝟙 ((pushforwardFiberFunctor p χ (f ≫ g)).obj x) := sorry

/-- Successive pushforwards of a fibre object are canonically isomorphic to its pushforward
along the composite. -/
noncomputable def pushforwardFiberCompIsoApp (p : F ⥤ C) (χ : p.op.Cleavage)
    {U V W : C} (f : U ⟶ V) (g : V ⟶ W) (x : p.Fiber U) :
    (pushforwardFiberFunctor p χ f ⋙ pushforwardFiberFunctor p χ g).obj x ≅
      (pushforwardFiberFunctor p χ (f ≫ g)).obj x where
  hom := pushforwardFiberCompHom p χ f g x
  inv := pushforwardFiberCompInv p χ f g x
  hom_inv_id := pushforwardFiberCompHom_inv_id p χ f g x
  inv_hom_id := pushforwardFiberCompInv_hom_id p χ f g x

/-- The objectwise composition comparison commutes with pushforward of fibre morphisms. -/
theorem pushforwardFiberCompIsoApp_naturality (p : F ⥤ C) (χ : p.op.Cleavage)
    {U V W : C} (f : U ⟶ V) (g : V ⟶ W) {x y : p.Fiber U} (φ : x ⟶ y) :
    (pushforwardFiberFunctor p χ f ⋙ pushforwardFiberFunctor p χ g).map φ ≫
        (pushforwardFiberCompIsoApp p χ f g y).hom =
      (pushforwardFiberCompIsoApp p χ f g x).hom ≫
        (pushforwardFiberFunctor p χ (f ≫ g)).map φ := sorry

/-- Successive pushforwards along `f` then `g` are naturally isomorphic to the pushforward along
`f ≫ g`. -/
noncomputable def pushforwardFiberCompIso (p : F ⥤ C) (χ : p.op.Cleavage)
    {U V W : C} (f : U ⟶ V) (g : V ⟶ W) :
    pushforwardFiberFunctor p χ f ⋙ pushforwardFiberFunctor p χ g ≅
      pushforwardFiberFunctor p χ (f ≫ g) :=
  NatIso.ofComponents (pushforwardFiberCompIsoApp p χ f g)
    (fun φ ↦ pushforwardFiberCompIsoApp_naturality p χ f g φ)

/-- The forward pushforward transport along equal base arrows is the unopposed inverse
reindexing transport. -/
noncomputable def pushforwardFiberCongrHom (p : F ⥤ C) (χ : p.op.Cleavage)
    {U V : C} {f g : U ⟶ V} (h : f = g) (x : p.Fiber U) :
    (pushforwardFiberFunctor p χ f).obj x ⟶ (pushforwardFiberFunctor p χ g).obj x :=
  fromOpFiberHom p
    ((Cleavage.Reindex.congrIso χ (congrArg Opposite.op h)).inv.app (toOpFiber p x))

/-- The inverse pushforward transport along equal base arrows is the unopposed forward
reindexing transport. -/
noncomputable def pushforwardFiberCongrInv (p : F ⥤ C) (χ : p.op.Cleavage)
    {U V : C} {f g : U ⟶ V} (h : f = g) (x : p.Fiber U) :
    (pushforwardFiberFunctor p χ g).obj x ⟶ (pushforwardFiberFunctor p χ f).obj x :=
  fromOpFiberHom p
    ((Cleavage.Reindex.congrIso χ (congrArg Opposite.op h)).hom.app (toOpFiber p x))

/-- Forward pushforward transport followed by inverse transport is the identity. -/
theorem pushforwardFiberCongrHom_inv_id (p : F ⥤ C) (χ : p.op.Cleavage)
    {U V : C} {f g : U ⟶ V} (h : f = g) (x : p.Fiber U) :
    pushforwardFiberCongrHom p χ h x ≫ pushforwardFiberCongrInv p χ h x =
      𝟙 ((pushforwardFiberFunctor p χ f).obj x) := sorry

/-- Inverse pushforward transport followed by forward transport is the identity. -/
theorem pushforwardFiberCongrInv_hom_id (p : F ⥤ C) (χ : p.op.Cleavage)
    {U V : C} {f g : U ⟶ V} (h : f = g) (x : p.Fiber U) :
    pushforwardFiberCongrInv p χ h x ≫ pushforwardFiberCongrHom p χ h x =
      𝟙 ((pushforwardFiberFunctor p χ g).obj x) := sorry

/-- Equal base arrows give canonically isomorphic pushforwards of each fibre object. -/
noncomputable def pushforwardFiberCongrIsoApp (p : F ⥤ C) (χ : p.op.Cleavage)
    {U V : C} {f g : U ⟶ V} (h : f = g) (x : p.Fiber U) :
    (pushforwardFiberFunctor p χ f).obj x ≅ (pushforwardFiberFunctor p χ g).obj x where
  hom := pushforwardFiberCongrHom p χ h x
  inv := pushforwardFiberCongrInv p χ h x
  hom_inv_id := pushforwardFiberCongrHom_inv_id p χ h x
  inv_hom_id := pushforwardFiberCongrInv_hom_id p χ h x

/-- Pushforward transport along equal base arrows is natural in the fibre object. -/
theorem pushforwardFiberCongrIsoApp_naturality (p : F ⥤ C) (χ : p.op.Cleavage)
    {U V : C} {f g : U ⟶ V} (h : f = g) {x y : p.Fiber U} (φ : x ⟶ y) :
    (pushforwardFiberFunctor p χ f).map φ ≫ (pushforwardFiberCongrIsoApp p χ h y).hom =
      (pushforwardFiberCongrIsoApp p χ h x).hom ≫
        (pushforwardFiberFunctor p χ g).map φ := sorry

/-- Equal base arrows induce naturally isomorphic pushforward fibre functors. -/
noncomputable def pushforwardFiberCongrIso (p : F ⥤ C) (χ : p.op.Cleavage)
    {U V : C} {f g : U ⟶ V} (h : f = g) :
    pushforwardFiberFunctor p χ f ≅ pushforwardFiberFunctor p χ g :=
  NatIso.ofComponents (pushforwardFiberCongrIsoApp p χ h)
    (fun φ ↦ pushforwardFiberCongrIsoApp_naturality p χ h φ)

/-- The 2-commutative square of fibre categories associated to a commuting square in the base. -/
noncomputable def fiberPushforwardSquare (p : F ⥤ C) (χ : p.op.Cleavage)
    {A A1 A2 P : C} {f1 : A1 ⟶ A} {f2 : A2 ⟶ A} {π1 : P ⟶ A1} {π2 : P ⟶ A2}
    (hw : π1 ≫ f1 = π2 ≫ f2) :
    CatCommSqOver (pushforwardFiberFunctor p χ f1) (pushforwardFiberFunctor p χ f2)
      (p.Fiber P) where
  fst := pushforwardFiberFunctor p χ π1
  snd := pushforwardFiberFunctor p χ π2
  iso :=
    pushforwardFiberCompIso p χ π1 f1 ≪≫
      pushforwardFiberCongrIso p χ hw ≪≫
      (pushforwardFiberCompIso p χ π2 f2).symm

/-- The first leg of the pushforward square is pushforward along its first base projection. -/
@[simp]
theorem fiberPushforwardSquare_fst (p : F ⥤ C) (χ : p.op.Cleavage)
    {A A1 A2 P : C} {f1 : A1 ⟶ A} {f2 : A2 ⟶ A} {π1 : P ⟶ A1} {π2 : P ⟶ A2}
    (hw : π1 ≫ f1 = π2 ≫ f2) :
    (fiberPushforwardSquare p χ hw).fst = pushforwardFiberFunctor p χ π1 := sorry

/-- The second leg of the pushforward square is pushforward along its second base projection. -/
@[simp]
theorem fiberPushforwardSquare_snd (p : F ⥤ C) (χ : p.op.Cleavage)
    {A A1 A2 P : C} {f1 : A1 ⟶ A} {f2 : A2 ⟶ A} {π1 : P ⟶ A1} {π2 : P ⟶ A2}
    (hw : π1 ≫ f1 = π2 ≫ f2) :
    (fiberPushforwardSquare p χ hw).snd = pushforwardFiberFunctor p χ π2 := sorry

/-- The comparison functor from the fibre over the apex into the 2-fibre product of the
pushforwards along the two base arrows. -/
noncomputable def fiberComparison (p : F ⥤ C) (χ : p.op.Cleavage)
    {A A1 A2 P : C} {f1 : A1 ⟶ A} {f2 : A2 ⟶ A} {π1 : P ⟶ A1} {π2 : P ⟶ A2}
    (hw : π1 ≫ f1 = π2 ≫ f2) :
    p.Fiber P ⥤
      (pushforwardFiberFunctor p χ f1) ⊡ (pushforwardFiberFunctor p χ f2) :=
  (fiberPushforwardSquare p χ hw).comparison

/-- The first object projection of the comparison is pushforward along the first base
projection. -/
@[simp]
theorem fiberComparison_obj_fst (p : F ⥤ C) (χ : p.op.Cleavage)
    {A A1 A2 P : C} {f1 : A1 ⟶ A} {f2 : A2 ⟶ A} {π1 : P ⟶ A1} {π2 : P ⟶ A2}
    (hw : π1 ≫ f1 = π2 ≫ f2) (y : p.Fiber P) :
    ((fiberComparison p χ hw).obj y).fst = (pushforwardFiberFunctor p χ π1).obj y := sorry

/-- The second object projection of the comparison is pushforward along the second base
projection. -/
@[simp]
theorem fiberComparison_obj_snd (p : F ⥤ C) (χ : p.op.Cleavage)
    {A A1 A2 P : C} {f1 : A1 ⟶ A} {f2 : A2 ⟶ A} {π1 : P ⟶ A1} {π2 : P ⟶ A2}
    (hw : π1 ≫ f1 = π2 ≫ f2) (y : p.Fiber P) :
    ((fiberComparison p χ hw).obj y).snd = (pushforwardFiberFunctor p χ π2).obj y := sorry

/-- The comparison object's structural isomorphism is the component of the pushforward
square's 2-cell. -/
@[simp]
theorem fiberComparison_obj_iso (p : F ⥤ C) (χ : p.op.Cleavage)
    {A A1 A2 P : C} {f1 : A1 ⟶ A} {f2 : A2 ⟶ A} {π1 : P ⟶ A1} {π2 : P ⟶ A2}
    (hw : π1 ≫ f1 = π2 ≫ f2) (y : p.Fiber P) :
    ((fiberComparison p χ hw).obj y).iso =
      (fiberPushforwardSquare p χ hw).iso.app y := sorry

/-- Comparison objects record the two pushforwards and the structural 2-cell of the
pushforward square. -/
theorem fiberComparison_spec (p : F ⥤ C) (χ : p.op.Cleavage)
    {A A1 A2 P : C} {f1 : A1 ⟶ A} {f2 : A2 ⟶ A} {π1 : P ⟶ A1} {π2 : P ⟶ A2}
    (hw : π1 ≫ f1 = π2 ≫ f2) (y : p.Fiber P) :
    ((fiberComparison p χ hw).obj y).fst = (pushforwardFiberFunctor p χ π1).obj y ∧
      ((fiberComparison p χ hw).obj y).snd = (pushforwardFiberFunctor p χ π2).obj y ∧
      ((fiberComparison p χ hw).obj y).iso =
        (fiberPushforwardSquare p χ hw).iso.app y := sorry

end CategoryTheory.Functor
