/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.PrincipalParts.BaseChange
public import ReasLib.Algebra.Module.PrincipalParts.RingHom

/-!
# Base change for principal parts along an explicit square of ring homomorphisms

This is the categorical, choice-explicit interface to principal-parts base change.  A commuting
square is supplied as four ring homomorphisms and an equality, while the module map lands in an
explicit restriction of scalars.  The typeclass-heavy presentation API remains an implementation
detail of this adapter.

@stack 09CP
-/

@[expose] public section

open CategoryTheory

universe u

noncomputable section

namespace PrincipalParts.RingHom.BaseChange

variable {A B A' B' : Type u}
variable [CommRing A] [CommRing B] [CommRing A'] [CommRing B']

/-- The canonical principal-parts morphism induced by an explicit commuting square of rings and
a compatible bundled module morphism. -/
@[stacks 09CP "explicit ring-square base change"]
noncomputable def map (σ : A →+* B) (σ' : A' →+* B') (a : A →+* A') (b : B →+* B')
    (sq : b.comp σ = σ'.comp a) (k : ℕ) {M : ModuleCat.{u} B} {M' : ModuleCat.{u} B'}
    (f : M ⟶ (ModuleCat.restrictScalars b).obj M') :
    PrincipalParts.RingHom.module σ M k ⟶
      (ModuleCat.restrictScalars b).obj (PrincipalParts.RingHom.module σ' M' k) :=
  -- Local instance justification (instance diamond): the four explicit sides and `sq` determine
  -- these scalar towers for this map; competing squares with the same rings need not agree.
  letI : Algebra A B := PrincipalParts.RingHom.algebra σ
  letI : Algebra A A' := PrincipalParts.RingHom.algebra a
  letI : Algebra B B' := PrincipalParts.RingHom.algebra b
  letI : Algebra A' B' := PrincipalParts.RingHom.algebra σ'
  letI : Algebra A B' := PrincipalParts.RingHom.algebra (σ'.comp a)
  letI : IsScalarTower A B B' := IsScalarTower.of_algebraMap_eq' sq.symm
  letI : IsScalarTower A A' B' := IsScalarTower.of_compHom A A' B'
  letI : Module A M := PrincipalParts.RingHom.sourceModule σ M
  letI : IsScalarTower A B M := IsScalarTower.of_compHom A B M
  letI : Module A' M' := PrincipalParts.RingHom.sourceModule σ' M'
  letI : Module B M' := PrincipalParts.RingHom.sourceModule b M'
  letI : Module A M' := PrincipalParts.RingHom.sourceModule (σ'.comp a) M'
  letI : IsScalarTower A' B' M' := IsScalarTower.of_compHom A' B' M'
  letI : IsScalarTower B B' M' := IsScalarTower.of_compHom B B' M'
  letI : IsScalarTower A A' M' := IsScalarTower.of_compHom A A' M'
  PrincipalParts.BaseChange.moduleMap
    (A := A) (B := B) (A' := A') (B' := B') (M := M) (M' := M') k f.hom

/-- Explicit base change sends the universal class of a section to the universal class of its
image. -/
@[simp]
theorem map_universalClass (σ : A →+* B) (σ' : A' →+* B') (a : A →+* A')
    (b : B →+* B') (sq : b.comp σ = σ'.comp a) (k : ℕ) {M : ModuleCat.{u} B}
    {M' : ModuleCat.{u} B'} (f : M ⟶ (ModuleCat.restrictScalars b).obj M') (m : M) :
    (map σ σ' a b sq k f).hom (PrincipalParts.RingHom.universalClass σ M k m) =
      PrincipalParts.RingHom.universalClass σ' M' k (f.hom m) := sorry

section Identity

/-- The square with identity maps on both base and total rings commutes. -/
theorem idSquare (σ : A →+* B) :
    (RingHom.id B).comp σ = σ.comp (RingHom.id A) := sorry

/-- Explicit base change along the identity square is the canonical identity-restriction map. -/
@[simp, stacks 09CP "identity base change"]
theorem map_id (σ : A →+* B) (k : ℕ) (M : ModuleCat.{u} B) :
    map σ σ (RingHom.id A) (RingHom.id B) (idSquare σ) k
        ((ModuleCat.restrictScalarsId B).inv.app M) =
      ((ModuleCat.restrictScalarsId B).inv.app
        (PrincipalParts.RingHom.module σ M k)) := sorry

end Identity

section Composition

variable {A'' B'' : Type u} [CommRing A''] [CommRing B'']

/-- Two composable commuting ring squares determine a commuting composite square. -/
theorem compSquare (σ : A →+* B) (σ' : A' →+* B') (σ'' : A'' →+* B'')
    (a : A →+* A') (b : B →+* B') (a' : A' →+* A'') (b' : B' →+* B'')
    (sq : b.comp σ = σ'.comp a) (sq' : b'.comp σ' = σ''.comp a') :
    (b'.comp b).comp σ = σ''.comp (a'.comp a) := sorry

/-- Explicit principal-parts base change is compatible with composition of commuting ring
squares and compatible module morphisms. -/
@[simp, stacks 09CP "composition of base change"]
theorem map_comp (σ : A →+* B) (σ' : A' →+* B') (σ'' : A'' →+* B'')
    (a : A →+* A') (b : B →+* B') (a' : A' →+* A'') (b' : B' →+* B'')
    (sq : b.comp σ = σ'.comp a) (sq' : b'.comp σ' = σ''.comp a') (k : ℕ)
    {M : ModuleCat.{u} B} {M' : ModuleCat.{u} B'} {M'' : ModuleCat.{u} B''}
    (f : M ⟶ (ModuleCat.restrictScalars b).obj M')
    (f' : M' ⟶ (ModuleCat.restrictScalars b').obj M'') :
    map σ σ' a b sq k f ≫
        (ModuleCat.restrictScalars b).map (map σ' σ'' a' b' sq' k f') ≫
        (ModuleCat.restrictScalarsComp' b b' (b'.comp b) rfl).inv.app
          (PrincipalParts.RingHom.module σ'' M'' k) =
      map σ σ'' (a'.comp a) (b'.comp b)
        (compSquare σ σ' σ'' a b a' b' sq sq') k
        (ModuleCat.RestrictScalars.homComp b b' f f') := sorry

end Composition

end PrincipalParts.RingHom.BaseChange

end
