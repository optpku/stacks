module

public import Mathlib.Algebra.Module.Equiv.Defs
public import stacks_project.Chap90.Lemma_90_19_7_TangentSpace

/-!
# Canonical comparison of identity-tangent spaces

The selected cleavage associator identifies `T_id Aut(x)` with `T_id Aut(x0)`,
where `x0` is the selected residue-field pushforward of `x`. The comparison is a
`k`-linear equivalence, not a definitional identification.
-/

@[expose] public section

noncomputable section

open CategoryTheory hiding Linear
open CategoryTheory.Limits
open ArtinianLocalAlgCat
open Opposite

universe u v w u₁ v₁ u₂ v₂

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]

namespace CategoryTheory.Functor

open Fiber Chosen

variable {C : Type u₁} [Category.{v₁} C]
variable {E : Type u₂} [Category.{v₂} E]

/-- Opposite-fibre isomorphism transported to the original fibre by `fromOp`. -/
def fromOpIso {q : E ⥤ C} {U : C} {y y' : q.op.Fiber (op U)} (e : y ≅ y') :
    fromOp y ≅ fromOp y' :=
  isoMk (Iso.unop (fiberInclusion.mapIso e.symm)) sorry

/-- Fibre isomorphism transported to the opposite fibre by `toOp`. -/
def toOpIso {q : E ⥤ C} {U : C} {x y : q.Fiber U} (e : x ≅ y) :
    toOp x ≅ toOp y :=
  isoMk (Iso.op (fiberInclusion.mapIso e.symm)) sorry

/-- The selected cleavage associator `(g ∘ f)_* x ≅ g_* (f_* x)` in the fibre over
the codomain of `g`. -/
def pushforwardObjCompIso (q : E ⥤ C) [q.op.IsFibered] {U V W : C}
    (f : U ⟶ V) (g : V ⟶ W) (x : q.Fiber U) :
    pushforwardObj q (f ≫ g) x ≅ pushforwardObj q g (pushforwardObj q f x) :=
  let yf := reindexObj q.op f.op (toOp x)
  let e :=
    Reindex.specifiedCompIsoApp q.op f.op g.op (f ≫ g).op op_comp.symm (toOp x)
  fromOpIso (e ≪≫ (reindex q.op g.op).mapIso (toOpFromOpIso yf).symm)

/-- `pushforwardObjCompIso` is the `fromOp` image of the selected specified-composite
comparison of `q.op`. -/
theorem pushforwardObjCompIso_eq (q : E ⥤ C) [q.op.IsFibered] {U V W : C}
    (f : U ⟶ V) (g : V ⟶ W) (x : q.Fiber U) :
    pushforwardObjCompIso q f g x =
      fromOpIso
        (Reindex.specifiedCompIsoApp q.op f.op g.op (f ≫ g).op op_comp.symm (toOp x) ≪≫
          (reindex q.op g.op).mapIso
            (toOpFromOpIso (reindexObj q.op f.op (toOp x))).symm) := sorry

variable (p : F ⥤ ArtinianLocalAlgCat Λ k)

/-- The selected residue-field pushforward `x0` of `x`. -/
def residuePushforward [p.op.IsFibered] (x : F) : p.Fiber (residue Λ k) :=
  pushforwardObj p (toResidue (p.obj x)) (ofObj p x)

/-- `residuePushforward p x` is the selected pushforward along `toResidue`. -/
theorem residuePushforward_eq [p.op.IsFibered] (x : F) :
    residuePushforward p x =
      pushforwardObj p (toResidue (p.obj x)) (ofObj p x) := sorry

/-- The total-category object underlying the selected residue pushforward. -/
abbrev residuePushforwardObj [p.op.IsFibered] (x : F) : F :=
  fiberInclusion.obj (residuePushforward p x)

/-- `residuePushforwardObj` is the underlying object of `residuePushforward`. -/
theorem residuePushforwardObj_eq [p.op.IsFibered] (x : F) :
    residuePushforwardObj p x = (residuePushforward p x).1 := sorry

/-- The selected residue pushforward lies over `k`. -/
theorem residuePushforwardObj_property [p.op.IsFibered] (x : F) :
    p.obj (residuePushforwardObj p x) = residue Λ k := sorry

/-- The composite base arrow `A → k → p.obj x0 → k → k[ε]`. -/
def residueDualNumberBase [p.op.IsFibered] (x : F) :
    p.obj x ⟶ dualNumber Λ k :=
  toResidue (p.obj x) ≫
    eqToHom (residuePushforward p x).2.symm ≫
      toResidue (p.obj (residuePushforwardObj p x)) ≫ residueToDualNumber Λ k

/-- The composite selected lift `x ⟶ x0 ⟶ (k[ε])_* x0`. -/
def residueDualNumberHom [p.op.IsFibered] (x : F) :
    (ofObj p x).1 ⟶ (idTangentSpaceObj p (residuePushforwardObj p x)).1 :=
  pushforwardHom p (toResidue (p.obj x)) (ofObj p x) ≫
    pushforwardHom p
      (toResidue (p.obj (residuePushforwardObj p x)) ≫ residueToDualNumber Λ k)
      (ofObj p (residuePushforwardObj p x))

/-- Strongly cocartesian factorization of a lift, with the `IsHomLift` hypothesis
taken as an explicit parameter. -/
def homLiftMap {R S S' : ArtinianLocalAlgCat Λ k} {a b b' : F}
    (f : R ⟶ S) (φ : a ⟶ b) (hφ : p.IsStronglyCocartesian f φ)
    (g : S ⟶ S') (f' : R ⟶ S') (hf' : f' = f ≫ g) (φ' : a ⟶ b')
    (hφ' : p.IsHomLift f' φ') : b ⟶ b' :=
  @IsStronglyCocartesian.map _ _ _ _ p R S a b f φ hφ S' b' g f' hf' φ' hφ'

/-- The composite residue-then-dual-number lift of `x` agrees with the dual-number
structure map of `x` after composing with an identity. -/
theorem idTangentSpaceObjIso_base_eq [p.op.IsFibered] (x : F) :
    residueDualNumberBase p x =
      (toResidue (p.obj x) ≫ residueToDualNumber Λ k) ≫ 𝟙 (dualNumber Λ k) := sorry

/-- The composite selected pushforward arrow `x ⟶ x0 ⟶ (k[ε])_* x0` lifts the
composite residue-then-dual-number algebra map. -/
theorem idTangentSpaceObjIso_isHomLift [p.op.IsFibered] (x : F) :
    p.IsHomLift (residueDualNumberBase p x) (residueDualNumberHom p x) := sorry

/-- The selected dual-number pushforward arrow of `x` lifts its displayed base
arrow. -/
theorem idTangentSpaceObjIso_inv_isHomLift [p.op.IsFibered] (x : F) :
    p.IsHomLift (toResidue (p.obj x) ≫ residueToDualNumber Λ k)
      (pushforwardHom p (toResidue (p.obj x) ≫ residueToDualNumber Λ k)
        (ofObj p x)) := sorry

/-- The composite `x ⟶ x0 ⟶ (k[ε])_* x0` is strongly cocartesian over the
composite residue-then-dual-number algebra map. -/
instance instIsStronglyCocartesian_residueDualNumberComp [p.op.IsFibered] (x : F) :
    p.IsStronglyCocartesian (residueDualNumberBase p x) (residueDualNumberHom p x) :=
  sorry

/-- Forward comparison of selected dual-number pushforwards of `x` and of `x0`. -/
def idTangentSpaceObjHom [p.op.IsFibered] (x : F) :
    (idTangentSpaceObj p x).1 ⟶ (idTangentSpaceObj p (residuePushforwardObj p x)).1 :=
  homLiftMap p
    (toResidue (p.obj x) ≫ residueToDualNumber Λ k)
    (pushforwardHom p (toResidue (p.obj x) ≫ residueToDualNumber Λ k) (ofObj p x))
    inferInstance
    (𝟙 (dualNumber Λ k))
    (residueDualNumberBase p x)
    (idTangentSpaceObjIso_base_eq p x)
    (residueDualNumberHom p x)
    (idTangentSpaceObjIso_isHomLift p x)

/-- Reverse comparison of selected dual-number pushforwards of `x0` and of `x`. -/
def idTangentSpaceObjInv [p.op.IsFibered] (x : F) :
    (idTangentSpaceObj p (residuePushforwardObj p x)).1 ⟶ (idTangentSpaceObj p x).1 :=
  homLiftMap p
    (residueDualNumberBase p x)
    (residueDualNumberHom p x)
    inferInstance
    (𝟙 (dualNumber Λ k))
    (toResidue (p.obj x) ≫ residueToDualNumber Λ k)
    (idTangentSpaceObjIso_base_eq p x).symm
    (pushforwardHom p (toResidue (p.obj x) ≫ residueToDualNumber Λ k) (ofObj p x))
    (idTangentSpaceObjIso_inv_isHomLift p x)

/-- The fibre isomorphism `(A → k[ε])_* x ≅ ((p.obj x0) → k[ε])_* x0` identifying
the two identity-tangent Aut-carriers. -/
def idTangentSpaceObjIso [p.op.IsFibered] (x : F) :
    idTangentSpaceObj p x ≅ idTangentSpaceObj p (residuePushforwardObj p x) :=
  isoMk
    { hom := idTangentSpaceObjHom p x
      inv := idTangentSpaceObjInv p x
      hom_inv_id := sorry
      inv_hom_id := sorry }
    sorry

/-- The underlying forward map of `idTangentSpaceObjIso` is `idTangentSpaceObjHom`. -/
theorem idTangentSpaceObjIso_hom [p.op.IsFibered] (x : F) :
    (idTangentSpaceObjIso p x).hom.1 = idTangentSpaceObjHom p x := sorry

/-- The group isomorphism of Aut groups induced by the selected fibre comparison. -/
def idTangentSpaceMulEquiv [IsFibered.InGroupoids p.op] (x : F) :
    idTangentSpace p x ≃* idTangentSpace p (residuePushforwardObj p x) where
  toFun α := ⟨Aut.autMulEquivOfIso (idTangentSpaceObjIso p x) α.val, sorry⟩
  invFun β := ⟨(Aut.autMulEquivOfIso (idTangentSpaceObjIso p x)).symm β.val, sorry⟩
  left_inv := sorry
  right_inv := sorry
  map_mul' := sorry

/-- `idTangentSpaceMulEquiv` acts by `Aut.autMulEquivOfIso` of `idTangentSpaceObjIso`. -/
theorem idTangentSpaceMulEquiv_apply [IsFibered.InGroupoids p.op] (x : F)
    (α : idTangentSpace p x) :
    (idTangentSpaceMulEquiv p x α : Aut (idTangentSpaceObj p (residuePushforwardObj p x))) =
      Aut.autMulEquivOfIso (idTangentSpaceObjIso p x) (α : Aut (idTangentSpaceObj p x)) :=
  sorry

/-- The canonical `k`-linear isomorphism `T_id Aut(x) ≃ T_id Aut(x0)`, where `x0` is
the selected residue-field pushforward of `x`. -/
def idTangentSpaceLinearEquiv [HasRimSchlessinger p] (x : F) :
    idTangentSpace p x ≃ₗ[k] idTangentSpace p (residuePushforwardObj p x) where
  toFun := (idTangentSpaceMulEquiv p x).toFun
  invFun := (idTangentSpaceMulEquiv p x).invFun
  map_add' := sorry
  map_smul' := sorry
  left_inv := sorry
  right_inv := sorry

/-- The underlying Aut-map of `idTangentSpaceLinearEquiv` is conjugation along
`idTangentSpaceObjIso`. -/
theorem idTangentSpaceLinearEquiv_apply [HasRimSchlessinger p] (x : F)
    (α : idTangentSpace p x) :
    (idTangentSpaceLinearEquiv p x α : Aut (idTangentSpaceObj p (residuePushforwardObj p x))) =
      Aut.autMulEquivOfIso (idTangentSpaceObjIso p x) (α : Aut (idTangentSpaceObj p x)) :=
  sorry

end CategoryTheory.Functor
