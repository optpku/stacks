module

public import Mathlib.RingTheory.Extension.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Equivalences of Algebra Extensions

`Algebra.Extension.Equiv P Q` packages an algebra equivalence between the
source rings of two extensions of the same target, together with compatibility
with their structure maps.  This is the invertible analogue of Mathlib's
`Algebra.Extension.Hom`.

@stack 04EF
-/

@[expose] public section

noncomputable section

open Algebra

namespace Algebra.Extension

universe u v w x y

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S]
variable {P : Extension.{w} R S} {Q : Extension.{x} R S}
variable {T : Extension.{y} R S}

/-- An equivalence of extensions is an algebra equivalence of their source
rings which commutes with the maps to the common target. -/
@[stacks 04EF "equivalence of algebra extensions", ext]
structure Equiv (P : Extension.{w} R S) (Q : Extension.{x} R S) where
  /-- The equivalence of source algebras. -/
  toAlgEquiv : P.Ring ≃ₐ[R] Q.Ring
  /-- Compatibility with the extension maps to the common target. -/
  algebraMap_toAlgEquiv :
    ∀ a, algebraMap Q.Ring S (toAlgEquiv a) = algebraMap P.Ring S a

attribute [simp] Equiv.algebraMap_toAlgEquiv

instance : CoeFun (P.Equiv Q) (fun _ ↦ P.Ring → Q.Ring) :=
  ⟨fun e ↦ e.toAlgEquiv⟩

/-- An equivalence of extensions, viewed as a hom of extensions. -/
noncomputable def Equiv.toHom (e : P.Equiv Q) : P.Hom Q :=
  Hom.ofAlgHom e.toAlgEquiv.toAlgHom <| by
    ext a
    exact e.algebraMap_toAlgEquiv a

@[simp]
theorem Equiv.toHom_toAlgHom (e : P.Equiv Q) :
    e.toHom.toAlgHom = e.toAlgEquiv.toAlgHom :=
  rfl

/-- The identity equivalence of an extension. -/
protected noncomputable def Equiv.refl (P : Extension.{w} R S) : P.Equiv P where
  toAlgEquiv := AlgEquiv.refl
  algebraMap_toAlgEquiv _ := rfl

/-- The inverse equivalence of extensions. -/
noncomputable def Equiv.symm (e : P.Equiv Q) : Q.Equiv P where
  toAlgEquiv := e.toAlgEquiv.symm
  algebraMap_toAlgEquiv a := by
    have h := e.algebraMap_toAlgEquiv (e.toAlgEquiv.symm a)
    simpa using h.symm

/-- Composition of equivalences of extensions. -/
noncomputable def Equiv.trans (e : P.Equiv Q) (f : Q.Equiv T) : P.Equiv T where
  toAlgEquiv := e.toAlgEquiv.trans f.toAlgEquiv
  algebraMap_toAlgEquiv a := by
    change algebraMap T.Ring S (f.toAlgEquiv (e.toAlgEquiv a)) = _
    rw [f.algebraMap_toAlgEquiv, e.algebraMap_toAlgEquiv]

@[simp]
theorem Equiv.refl_apply (P : Extension.{w} R S) (a : P.Ring) :
    Equiv.refl P a = a :=
  rfl

@[simp]
theorem Equiv.symm_apply_apply (e : P.Equiv Q) (a : P.Ring) :
    e.symm (e a) = a :=
  e.toAlgEquiv.symm_apply_apply a

@[simp]
theorem Equiv.apply_symm_apply (e : P.Equiv Q) (a : Q.Ring) :
    e (e.symm a) = a :=
  e.toAlgEquiv.apply_symm_apply a

@[simp]
theorem Equiv.trans_apply (e : P.Equiv Q) (f : Q.Equiv T) (a : P.Ring) :
    e.trans f a = f (e a) :=
  rfl

end Algebra.Extension
