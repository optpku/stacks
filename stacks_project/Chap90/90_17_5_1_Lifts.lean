module

public import Mathlib.CategoryTheory.FiberedCategory.Cocartesian
public import stacks_project.Chap90.Definition_90_17_1_ObjectLift
public import stacks_project.Chap90.Remarks_90_5_2_Pushforward

/-!
# Transport of lift-sets along a base isomorphism

A base isomorphism `e : B ≅ B'` over `A` induces a bijection on isomorphism classes of
lifts of a fibre object `x` along the two structure maps to `A`, by cofibered pushforward
of lift domains along `e.hom`.
-/

@[expose] public section

universe v₁ u₁ v₂ u₂

open CategoryTheory
open Functor Fiber

namespace CategoryTheory.Functor

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₂} 𝒳]
variable {p : 𝒳 ⥤ 𝒮}

/-- Hom-lifts of `p` reverse to hom-lifts of `p.op`. -/
instance instIsHomLift_op {R S : 𝒮} {a b : 𝒳} {f : R ⟶ S} {φ : a ⟶ b}
    [p.IsHomLift f φ] : p.op.IsHomLift f.op φ.op := sorry

/-- The strongly cocartesian property of a bundled lift is a typeclass instance. -/
instance instIsStronglyCocartesian_baseLift {x : 𝒳} {V : 𝒮} {g : p.obj x ⟶ V}
    (l : StronglyCocartesianLift p g) : p.IsStronglyCocartesian g l.hom :=
  l.isStronglyCocartesian

/-- Reindex a lift along an equality of base morphisms. The underlying total morphism
is unchanged. -/
def ObjectLift.reindex {R S : 𝒮} {f g : R ⟶ S} (h : f = g) {x : p.Fiber S}
    (a : ObjectLift p f x) : ObjectLift p g x :=
  ⟨a.val, sorry⟩

/-- `ObjectLift.reindex` preserves the underlying total morphism. -/
theorem ObjectLift.reindex_hom {R S : 𝒮} {f g : R ⟶ S} (h : f = g) {x : p.Fiber S}
    (a : ObjectLift p f x) : (ObjectLift.reindex h a).hom = a.hom := sorry

/-- Reindexing the domain of `u` by `eqToHom` preserves the hom-lift of a lift along
`u ≫ f`. -/
instance instIsHomLift_domainReindex {R R' S : 𝒮} (u : R ⟶ R') (f : R' ⟶ S)
    {x : p.Fiber S} (a : ObjectLift p (u ≫ f) x) :
    p.IsHomLift ((eqToHom (IsHomLift.domain_eq p (u ≫ f) a.hom) ≫ u) ≫ f) a.hom :=
  sorry

/-- Push a lift of `x` along `f` forward along a base isomorphism `e : B ≅ B'` over `A`,
obtaining a lift along `f'`. -/
noncomputable def ObjectLift.alongBaseIso [IsFibered.InGroupoids p.op]
    {B B' A : 𝒮} {f : B ⟶ A} {f' : B' ⟶ A} (e : B ≅ B')
    (he : e.hom ≫ f' = f) {x : p.Fiber A} (a : ObjectLift p f x) :
    ObjectLift p f' x :=
  let a' := ObjectLift.reindex he.symm a
  let u' : p.obj a'.left ⟶ B' :=
    eqToHom (IsHomLift.domain_eq p (e.hom ≫ f') a'.hom) ≫ e.hom
  let l := StronglyCocartesianLift.ofCleavage (cleavageOp p) u'
  ⟨Over.mk (IsStronglyCocartesian.map p u' l.hom (rfl : u' ≫ f' = u' ≫ f') a'.hom),
    sorry⟩

/-- The transported lift lies over `f'` with domain over `B'`. -/
theorem ObjectLift.alongBaseIso_spec [IsFibered.InGroupoids p.op]
    {B B' A : 𝒮} {f : B ⟶ A} {f' : B' ⟶ A} (e : B ≅ B')
    (he : e.hom ≫ f' = f) {x : p.Fiber A} (a : ObjectLift p f x) :
    p.IsHomLift f' (ObjectLift.alongBaseIso e he a).hom ∧
      p.obj (ObjectLift.alongBaseIso e he a).left = B' := sorry

/-- Inverting a commuting triangle `e.hom ≫ f' = f` yields `e.inv ≫ f = f'`. -/
theorem iso_inv_comp_of_hom_comp {B B' A : 𝒮} (e : B ≅ B') {f : B ⟶ A} {f' : B' ⟶ A}
    (he : e.hom ≫ f' = f) : e.inv ≫ f = f' := sorry

/-- Transport of isomorphism classes of lifts along a base isomorphism over `A`. -/
noncomputable def liftsCongr [IsFibered.InGroupoids p.op]
    {B B' A : 𝒮} {f : B ⟶ A} {f' : B' ⟶ A} (e : B ≅ B')
    (he : e.hom ≫ f' = f) (x : p.Fiber A) :
    lifts p f x ≃ lifts p f' x where
  toFun := fun q =>
    Quotient.liftOn q (fun a => Quotient.mk'' (ObjectLift.alongBaseIso e he a)) sorry
  invFun := fun q =>
    Quotient.liftOn q
      (fun a => Quotient.mk'' (ObjectLift.alongBaseIso e.symm (iso_inv_comp_of_hom_comp e he) a))
      sorry
  left_inv := sorry
  right_inv := sorry

/-- On a represented class, `liftsCongr` is `ObjectLift.alongBaseIso` of the representative. -/
theorem liftsCongr_apply [IsFibered.InGroupoids p.op]
    {B B' A : 𝒮} {f : B ⟶ A} {f' : B' ⟶ A} (e : B ≅ B')
    (he : e.hom ≫ f' = f) {x : p.Fiber A} (a : ObjectLift p f x) :
    liftsCongr e he x (Quotient.mk'' a) = Quotient.mk'' (ObjectLift.alongBaseIso e he a) := sorry

end CategoryTheory.Functor
