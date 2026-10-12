/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.CofilteredSystem
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Hom inverse systems

This file owns the contravariant Hom system attached to an arbitrary diagram.  No colimit,
preadditive structure, or module structure is needed at this layer.
-/

@[expose] public section

universe uI vI uC vC uD vD uT uT'

namespace CategoryTheory.Functor

variable {I : Type uI} [Category.{vI} I]
variable {C : Type uC} [Category.{vC} C]

/-- The inverse system `i ↦ Hom(F.obj i, N)` attached to a diagram `F`. -/
@[stacks 059A "Hom inverse system"]
abbrev homInverseSystem (F : I ⥤ C) (N : C) := F.op ⋙ yoneda.obj N

/-- Every contravariant representable system associated to `F` is Mittag-Leffler. -/
@[stacks 059E "all-target Hom criterion"]
abbrev HomMittagLeffler (F : I ⥤ C) : Prop :=
  ∀ N : C, (F.homInverseSystem N).IsMittagLeffler

namespace IsMittagLeffler

variable {F G : I ⥤ Type uT}

/-- The Mittag-Leffler condition transfers across a pointwise equivalence compatible with the
transition maps.  The two systems may take values in different universes. -/
theorem of_equiv {F : I ⥤ Type uT} {G : I ⥤ Type uT'}
    (hF : F.IsMittagLeffler) (e : ∀ i, F.obj i ≃ G.obj i)
    (he : ∀ {i j} (f : i ⟶ j) (x : F.obj i),
      e j (F.map f x) = G.map f (e i x)) :
    G.IsMittagLeffler := by
  intro j
  obtain ⟨i, f, hf⟩ := hF j
  refine ⟨i, f, ?_⟩
  intro k g y hy
  obtain ⟨x, rfl⟩ := hy
  obtain ⟨z, hz⟩ := hf g ⟨(e i).symm x, rfl⟩
  refine ⟨e k z, ?_⟩
  calc
    G.map g (e k z) = e j (F.map g z) := (he g z).symm
    _ = e j (F.map f ((e i).symm x)) := by rw [hz]
    _ = G.map f (e i ((e i).symm x)) := he f ((e i).symm x)
    _ = G.map f x := by simp

/-- Pointwise equivalent systems compatible with their transition maps satisfy the
Mittag-Leffler condition simultaneously, even when their values live in different universes. -/
theorem iff_of_equiv {F : I ⥤ Type uT} {G : I ⥤ Type uT'}
    (e : ∀ i, F.obj i ≃ G.obj i)
    (he : ∀ {i j} (f : i ⟶ j) (x : F.obj i),
      e j (F.map f x) = G.map f (e i x)) :
    F.IsMittagLeffler ↔ G.IsMittagLeffler := by
  constructor
  · intro hF
    exact hF.of_equiv e he
  · intro hG
    apply hG.of_equiv (fun i ↦ (e i).symm)
    intro i j f x
    apply (e j).injective
    simp only [Equiv.apply_symm_apply]
    rw [he]
    simp

/-- The Mittag-Leffler condition on a type-valued functor is invariant under natural
isomorphism. -/
@[stacks 059A "isomorphism invariance"]
theorem of_iso (hF : F.IsMittagLeffler) (e : F ≅ G) : G.IsMittagLeffler := by
  intro j
  obtain ⟨i, f, hf⟩ := hF j
  refine ⟨i, f, ?_⟩
  intro k g y hy
  obtain ⟨x, rfl⟩ := hy
  obtain ⟨z, hz⟩ := hf g ⟨e.inv.app i x, rfl⟩
  refine ⟨e.hom.app k z, ?_⟩
  calc
    G.map g (e.hom.app k z) = e.hom.app j (F.map g z) := by
      simpa using (congrFun (e.hom.naturality g) z).symm
    _ = e.hom.app j (F.map f (e.inv.app i x)) := by rw [hz]
    _ = G.map f (e.hom.app i (e.inv.app i x)) := by
      simpa using congrFun (e.hom.naturality f) (e.inv.app i x)
    _ = G.map f x := by simp

/-- Naturally isomorphic type-valued functors satisfy the Mittag-Leffler condition
simultaneously. -/
@[stacks 059A "isomorphism invariance iff"]
theorem iff_of_iso (e : F ≅ G) : F.IsMittagLeffler ↔ G.IsMittagLeffler :=
  ⟨fun hF ↦ hF.of_iso e, fun hG ↦ hG.of_iso e.symm⟩

end IsMittagLeffler

namespace FullyFaithful

variable {D : Type uD} [Category.{vD} D] {G : C ⥤ D}

/-- A fully faithful functor preserves and reflects the Mittag-Leffler condition on every Hom
inverse system. -/
@[stacks 05CR "fully faithful Hom comparison"]
theorem homInverseSystem_iff (hG : G.FullyFaithful)
    (F : I ⥤ C) (N : C) :
    ((F ⋙ G).homInverseSystem (G.obj N)).IsMittagLeffler ↔
      (F.homInverseSystem N).IsMittagLeffler := by
  apply CategoryTheory.Functor.IsMittagLeffler.iff_of_equiv
    (fun i ↦ (hG.homEquiv (X := F.obj i.unop) (Y := N)).symm)
  intro i j f q
  change hG.preimage (G.map (F.map f.unop) ≫ q) =
    F.map f.unop ≫ hG.preimage q
  simp

end FullyFaithful

end CategoryTheory.Functor
