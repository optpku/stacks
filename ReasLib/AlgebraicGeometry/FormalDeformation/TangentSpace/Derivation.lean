/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.TangentSpace
public import ReasLib.AlgebraicGeometry.FormalDeformation.DualNumber.Derivation
public import ReasLib.CategoryTheory.Fibered.Cleavage.Basic.Reindex.Functor

/-!
# The canonical tangent vector associated to a derivation

Pushing a residue-fibre object forward along the dual-number morphism associated to a
derivation determines a tangent vector independent of the residue-fibre representative.
-/

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]
variable (p : F ⥤ ArtinianLocalAlgCat Λ k)

namespace CategoryTheory.Functor.tangentSpace

set_option backward.privateInPublic true in
/-- A predeformation category has an object in its residue fibre. -/
private noncomputable def residueFiberPt [IsPredeformationCategory p] :
    p.Fiber (residue Λ k) :=
  Classical.choice IsPredeformationCategory.nonempty_residueFiber

set_option backward.privateInPublic true in
/-- Pushforward of a residue-fibre object along the morphism associated to a derivation,
computed by reindexing in the opposite category. -/
private noncomputable def pushforwardResidueFiber [IsPredeformationCategory p]
    (x0 : p.Fiber (residue Λ k)) (D : Derivation Λ k k) : p.Fiber (dualNumber Λ k) :=
  let oppositeObject : p.op.Fiber (Opposite.op (residue Λ k)) :=
    ⟨Opposite.op x0.1, congrArg Opposite.op x0.property⟩
  let oppositeCleavage := @Cleavage.ofIsFibered _ _ _ _ p.op
    (IsPredeformationCategory.isCofiberedInGroupoids (p := p)).toIsFibered
  let pushedObject :=
    (oppositeCleavage.reindex (derivationToDualNumber D).op).obj oppositeObject
  ⟨Opposite.unop pushedObject.1, congrArg Opposite.unop pushedObject.property⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- A residue-fibre object and a derivation determine the tangent vector represented by
the pushforward of that object along the associated dual-number morphism. -/
noncomputable def ofDerivationWith [IsPredeformationCategory p]
    (x0 : p.Fiber (residue Λ k)) : Derivation Λ k k → tangentSpace p :=
  fun derivation ↦ tangentSpace.mk p (pushforwardResidueFiber p x0 derivation)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The canonical map from base-linear derivations of the residue field to the tangent
space of a predeformation category. -/
noncomputable def ofDerivation [IsPredeformationCategory p] :
    Derivation Λ k k → tangentSpace p :=
  ofDerivationWith p (residueFiberPt p)

/-- The canonical tangent vector associated to a derivation agrees with the pushforward
class obtained from any residue-fibre representative. -/
theorem ofDerivation_apply [IsPredeformationCategory p]
    (x0 : p.Fiber (residue Λ k)) (D : Derivation Λ k k) :
    ofDerivation p D = ofDerivationWith p x0 D := sorry

end CategoryTheory.Functor.tangentSpace
