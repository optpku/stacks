module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.CategoryTheory.Conj
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap90.Definition_90_19_2
public import stacks_project.Chap90.Remark_90_19_3_InfAut

/-!
# Independence of infinitesimal automorphisms from the choice of pushforward

For a category cofibered in groupoids over `C_Λ`, the group
`infinitesimalAutomorphismsAt p x0 x0' φ` attached to a dual-number pushforward of `x0`
is independent of that pushforward up to the canonical `MulEquiv` of any two
pushforwards, and is functorial in residue-fibre isomorphisms. In particular
`Aut x0` acts by conjugation through `fiberAutHom`.
-/

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat
open Functor Fiber

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]
variable (p : F ⥤ ArtinianLocalAlgCat Λ k)
variable [IsFibered.InGroupoids p.op]

namespace CategoryTheory.Functor

/-- Remark 90.19.3 (1): up to canonical isomorphism, `infinitesimalAutomorphismsAt p x0 x0' φ`
does not depend on the choice of pushforward `x0 ⟶ x0'`, because any two pushforwards are
canonically isomorphic. -/
@[stacks 06JR]
noncomputable def infAutAtIso_of_pushforward
    {x0 : p.Fiber (residue Λ k)} {x0' y0' : p.Fiber (dualNumber Λ k)}
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    (ψ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj y0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ]
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) ψ] :
    infinitesimalAutomorphismsAt p x0 x0' φ ≃*
      infinitesimalAutomorphismsAt p x0 y0' ψ where
  toFun a := ⟨(fiberIso_of_pushforward p φ ψ).conjAut a.val, sorry⟩
  invFun b := ⟨(fiberIso_of_pushforward p φ ψ).symm.conjAut b.val, sorry⟩
  left_inv := sorry
  right_inv := sorry
  map_mul' := sorry

/-- The comparison of clause (1) is conjugation along the unique vertical isomorphism of
pushforward targets. -/
theorem infAutAtIso_of_pushforward_apply
    {x0 : p.Fiber (residue Λ k)} {x0' y0' : p.Fiber (dualNumber Λ k)}
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    (ψ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj y0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ]
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) ψ]
    (a : infinitesimalAutomorphismsAt p x0 x0' φ) :
    (infAutAtIso_of_pushforward p φ ψ a).val =
      (fiberIso_of_pushforward p φ ψ).conjAut a.val := sorry

/-- Remark 90.19.3 (2): a fibre isomorphism `x0 ≅ y0` in `p.Fiber (residue Λ k)` induces
`infinitesimalAutomorphismsAt p x0 x0' φ ≃* infinitesimalAutomorphismsAt p y0 y0' ψ`
depending only on that isomorphism. -/
@[stacks 06JR]
noncomputable def infAutAtIso_of_fiberIso
    {x0 y0 : p.Fiber (residue Λ k)} {x0' y0' : p.Fiber (dualNumber Λ k)}
    (α : x0 ≅ y0)
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    (ψ : fiberInclusion.obj y0 ⟶ fiberInclusion.obj y0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ]
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) ψ] :
    infinitesimalAutomorphismsAt p x0 x0' φ ≃*
      infinitesimalAutomorphismsAt p y0 y0' ψ where
  toFun a := ⟨(fiberIso_of_fiberIso p α φ ψ).conjAut a.val, sorry⟩
  invFun b := ⟨(fiberIso_of_fiberIso p α φ ψ).symm.conjAut b.val, sorry⟩
  left_inv := sorry
  right_inv := sorry
  map_mul' := sorry

/-- The comparison of clause (2) is conjugation along the vertical isomorphism of pushforward
targets determined by the residue-fibre isomorphism `α`. -/
theorem infAutAtIso_of_fiberIso_apply
    {x0 y0 : p.Fiber (residue Λ k)} {x0' y0' : p.Fiber (dualNumber Λ k)}
    (α : x0 ≅ y0)
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    (ψ : fiberInclusion.obj y0 ⟶ fiberInclusion.obj y0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ]
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) ψ]
    (a : infinitesimalAutomorphismsAt p x0 x0' φ) :
    (infAutAtIso_of_fiberIso p α φ ψ a).val =
      (fiberIso_of_fiberIso p α φ ψ).conjAut a.val := sorry

/-- After transporting by the clause (1) comparisons, the clause (2) `MulEquiv` attached to
`α : x0 ≅ y0` is independent of the chosen dual-number pushforwards of `x0` and `y0`. -/
theorem infAutAtIso_of_fiberIso_independent_of_pushforward
    {x0 y0 : p.Fiber (residue Λ k)}
    {x0' x0'' y0' y0'' : p.Fiber (dualNumber Λ k)}
    (α : x0 ≅ y0)
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    (φ' : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0'')
    (ψ : fiberInclusion.obj y0 ⟶ fiberInclusion.obj y0')
    (ψ' : fiberInclusion.obj y0 ⟶ fiberInclusion.obj y0'')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ]
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ']
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) ψ]
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) ψ'] :
    (infAutAtIso_of_pushforward p φ φ').trans (infAutAtIso_of_fiberIso p α φ' ψ') =
      (infAutAtIso_of_fiberIso p α φ ψ).trans (infAutAtIso_of_pushforward p ψ ψ') := sorry

/-- Remark 90.19.3 (3): in particular `Aut x0` acts on
`infinitesimalAutomorphismsAt p x0 x0' φ` by the `α := id` specialization of clause (2),
equivalently by conjugation through `fiberAutHom` along `φ`. -/
@[stacks 06JR, instance]
noncomputable instance instMulDistribMulAction_aut_infAutAt
    {x0 : p.Fiber (residue Λ k)} {x0' : p.Fiber (dualNumber Λ k)}
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ] :
    MulDistribMulAction (Aut x0) (infinitesimalAutomorphismsAt p x0 x0' φ) where
  smul β a := infAutAtIso_of_fiberIso p β φ φ a
  one_smul := sorry
  mul_smul := sorry
  smul_mul := sorry
  smul_one := sorry

/-- The Aut action of clause (3) is conjugation by `fiberAutHom` along the dual-number
pushforward. -/
theorem infAutAt_smul_eq_fiberAutHom_conj
    {x0 : p.Fiber (residue Λ k)} {x0' : p.Fiber (dualNumber Λ k)}
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ]
    (β : Aut x0) (a : infinitesimalAutomorphismsAt p x0 x0' φ) :
    (β • a).val =
      fiberAutHom p (residueToDualNumber Λ k) φ β * a.val *
        (fiberAutHom p (residueToDualNumber Λ k) φ β)⁻¹ := sorry

end CategoryTheory.Functor
