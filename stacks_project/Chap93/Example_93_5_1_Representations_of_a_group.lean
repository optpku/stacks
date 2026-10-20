/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap90.Remark_90_6_4
public import ReasLib.AlgebraicGeometry.FormalDeformation.GroupRepresentation
public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.Over
public meta import Lean.Elab.StructInst
import StacksCheckRecall

/-! # Deformation category of a group representation -/

@[expose] public section

open CategoryTheory
open Functor

universe u

namespace GroupRepCat

public meta section

open Lean.Parser.Term

/-- Compatibility elaboration sends the legacy six-field representation record to
`GroupRepCat.of`; structure syntax at every other expected type is left unchanged. -/
@[term_elab Lean.Parser.Term.structInst]
def elabLegacyRecord : Lean.Elab.Term.TermElab := fun stx expectedType? => do
  let some expectedType := expectedType? | Lean.Elab.throwUnsupportedSyntax
  let expectedType ← Lean.instantiateMVars expectedType
  unless expectedType.getAppFn.isConstOf ``GroupRepCat do
    Lean.Elab.throwUnsupportedSyntax
  let `({ $[$sources,* with]? $[$fields],* $[: $ascription?]? }) := stx
    | Lean.Elab.throwUnsupportedSyntax
  if sources.isSome || ascription?.isSome || fields.size != 6 then
    Lean.Elab.throwUnsupportedSyntax
  let mut values : Array (Lean.Name × Lean.TSyntax `term) := #[]
  for field in fields do
    let `(structInstField| $name:ident := $value) := field
      | Lean.Elab.throwUnsupportedSyntax
    let name := name.getId.eraseMacroScopes
    unless #[`base, `module, `addCommGroup, `isModule, `finiteProjective, `rho].contains name do
      Lean.Elab.throwUnsupportedSyntax
    if values.any (fun entry => entry.1 == name) then
      Lean.Elab.throwUnsupportedSyntax
    values := values.push (name, value)
  let some (_, base) := values.find? (fun entry => entry.1 == `base)
    | Lean.Elab.throwUnsupportedSyntax
  let some (_, module) := values.find? (fun entry => entry.1 == `module)
    | Lean.Elab.throwUnsupportedSyntax
  let some (_, addCommGroup) := values.find? (fun entry => entry.1 == `addCommGroup)
    | Lean.Elab.throwUnsupportedSyntax
  let some (_, isModule) := values.find? (fun entry => entry.1 == `isModule)
    | Lean.Elab.throwUnsupportedSyntax
  let some (_, finiteProjective) := values.find? (fun entry => entry.1 == `finiteProjective)
    | Lean.Elab.throwUnsupportedSyntax
  let some (_, rho) := values.find? (fun entry => entry.1 == `rho)
    | Lean.Elab.throwUnsupportedSyntax
  let term ← `(GroupRepCat.of $base $module (addCommGroup := $addCommGroup)
    (isModule := $isModule) $finiteProjective $rho)
  Lean.Elab.Term.elabTerm term expectedType

end

variable (Γ Λ k : Type u) [Group Γ] [CommRing Λ] [IsNoetherianRing Λ] [Field k]
  [Algebra Λ k] [Module.Finite Λ k]
variable {V : Type u} [AddCommGroup V] [Module k V] [Module.Finite k V]
variable (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)

/- Example 93.5.1 (Representations of a group)
Let `Γ` be a group. The category `GroupRepCat Γ Λ k` has objects triples
`(A, M, ρ)` consisting of an object `A` of `ArtinianLocalAlgCat Λ k`, a finite
projective `A`-module `M`, and a homomorphism
`ρ : Γ →* LinearMap.GeneralLinearGroup A.carrier M`. A morphism `(f, g)` from
`(B, N, τ)` to `(A, M, ρ)` consists of a morphism `f : B ⟶ A` in
`ArtinianLocalAlgCat Λ k` together with a map `g : N → M` which is `f`-linear
and `Γ`-equivariant and induces an isomorphism `N ⊗[B, f] A ≃ M`. The functor
`GroupRepCat.forget` sends `(A, M, ρ)` to `A` and `(f, g)` to `f`, and is
cofibered in groupoids. Given a finite-dimensional `k`-vector space `V` and a
representation `ρ0 : Γ →* LinearMap.GeneralLinearGroup k V`, the object
`x0 = (k, V, ρ0)` is `ofResidue ρ0`, and `deformation ρ0` is the residue-fibre
slice `F_{x0} = Over (Fiber.fiberInclusion.obj (residueObj Γ Λ k ρ0))`. -/
@[stacks 0D3J] #check (GroupRepCat.deformation Γ Λ k ρ0 : Type (u + 1))

end GroupRepCat
