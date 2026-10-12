/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Module.Product

/-!
# Projective Modules over Product Semirings

This leaf contains the projectivity criterion associated to the idempotent decomposition of a
module over a product semiring.  It is deliberately separate from finite generation.
-/

@[expose] public section

universe u v w

namespace Module.Projective

variable (R : Type u) (S : Type v) [Semiring R] [Semiring S]

open Module.Product

private def leftFactorProjection (M : Type w) [AddCommMonoid M] [Module (R × S) M] :
    M →ₗ[R × S] leftSubmodule R S M :=
  (LinearMap.fst (R × S) (leftSubmodule R S M) (rightSubmodule R S M)).comp
    (factorLinearEquiv R S M).toLinearMap

private def rightFactorProjection (M : Type w) [AddCommMonoid M] [Module (R × S) M] :
    M →ₗ[R × S] rightSubmodule R S M :=
  (LinearMap.snd (R × S) (leftSubmodule R S M) (rightSubmodule R S M)).comp
    (factorLinearEquiv R S M).toLinearMap

private theorem leftFactorProjection_comp_subtype (M : Type w) [AddCommMonoid M]
    [Module (R × S) M] :
    (leftFactorProjection R S M).comp (leftSubmodule R S M).subtype = LinearMap.id := by
  ext l
  change leftIdempotent R S • l.1 = l.1
  have h := left_smul_add_right_smul R S M l.1
  rw [l.property, add_zero] at h
  exact h

private theorem rightFactorProjection_comp_subtype (M : Type w) [AddCommMonoid M]
    [Module (R × S) M] :
    (rightFactorProjection R S M).comp (rightSubmodule R S M).subtype = LinearMap.id := by
  ext r
  change rightIdempotent R S • r.1 = r.1
  have h := left_smul_add_right_smul R S M r.1
  rw [r.property, zero_add] at h
  exact h

private theorem left_of_product (M : Type w) [AddCommMonoid M] [Module (R × S) M]
    [Module.Projective (R × S) M] :
    Module.Projective R (leftSubmodule R S M) := by
  let L := leftSubmodule R S M
  letI : Module.Projective (R × S) L :=
    Module.Projective.of_split L.subtype (leftFactorProjection R S M)
      (leftFactorProjection_comp_subtype R S M)
  apply Module.Projective.of_lifting_property''
  intro f hf
  letI : Module (R × S) (L →₀ R) := Module.compHom (L →₀ R) (RingHom.fst R S)
  let fProd : (L →₀ R) →ₗ[R × S] L :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := by
        intro a x
        apply Subtype.ext
        change (f (a.1 • x)).1 = a • (f x).1
        rw [f.map_smul]
        exact (leftSubmodule_smul_val R S M a (f x)).symm }
  obtain ⟨hProd, hh⟩ :=
    Module.projective_lifting_property fProd (LinearMap.id : L →ₗ[R × S] L) hf
  let h : L →ₗ[R] L →₀ R :=
    { toFun := hProd
      map_add' := hProd.map_add
      map_smul' := by
        intro r l
        have hin : (((r, (0 : S)) : R × S) • l) = r • l := by
          apply Subtype.ext
          exact (leftModule_smul_val R S M r l).symm
        calc
          hProd (r • l) = hProd (((r, (0 : S)) : R × S) • l) := by rw [hin]
          _ = ((r, (0 : S)) : R × S) • hProd l := hProd.map_smul _ _
          _ = r • hProd l := rfl }
  refine ⟨h, ?_⟩
  ext l
  simpa [fProd, h] using congrArg Subtype.val (DFunLike.congr_fun hh l)

private theorem right_of_product (M : Type w) [AddCommMonoid M] [Module (R × S) M]
    [Module.Projective (R × S) M] :
    Module.Projective S (rightSubmodule R S M) := by
  let Q := rightSubmodule R S M
  letI : Module.Projective (R × S) Q :=
    Module.Projective.of_split Q.subtype (rightFactorProjection R S M)
      (rightFactorProjection_comp_subtype R S M)
  apply Module.Projective.of_lifting_property''
  intro f hf
  letI : Module (R × S) (Q →₀ S) := Module.compHom (Q →₀ S) (RingHom.snd R S)
  let fProd : (Q →₀ S) →ₗ[R × S] Q :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := by
        intro a x
        apply Subtype.ext
        change (f (a.2 • x)).1 = a • (f x).1
        rw [f.map_smul]
        exact (rightSubmodule_smul_val R S M a (f x)).symm }
  obtain ⟨hProd, hh⟩ :=
    Module.projective_lifting_property fProd (LinearMap.id : Q →ₗ[R × S] Q) hf
  let h : Q →ₗ[S] Q →₀ S :=
    { toFun := hProd
      map_add' := hProd.map_add
      map_smul' := by
        intro s q
        have hin : ((((0 : R), s) : R × S) • q) = s • q := by
          apply Subtype.ext
          exact (rightModule_smul_val R S M s q).symm
        calc
          hProd (s • q) = hProd ((((0 : R), s) : R × S) • q) := by rw [hin]
          _ = (((0 : R), s) : R × S) • hProd q := hProd.map_smul _ _
          _ = s • hProd q := rfl }
  refine ⟨h, ?_⟩
  ext q
  simpa [fProd, h] using congrArg Subtype.val (DFunLike.congr_fun hh q)

private theorem product_left_of_left (M : Type w) [AddCommMonoid M] [Module (R × S) M]
    [Module.Projective R (leftSubmodule R S M)] :
    Module.Projective (R × S) (leftSubmodule R S M) := by
  let L := leftSubmodule R S M
  apply Module.Projective.of_lifting_property''
  intro f hf
  let F := L →₀ (R × S)
  let FL := leftSubmodule R S F
  let fLeft : FL →ₗ[R] L :=
    { toFun := fun x ↦ f x.1
      map_add' := by intros; simp
      map_smul' := by
        intro r x
        apply Subtype.ext
        change (f ((r • x).1)).1 = (r • f x.1).1
        rw [leftModule_smul_val, f.map_smul]
        exact (leftModule_smul_val R S M r (f x.1)).symm }
  have hfLeft : Function.Surjective fLeft := by
    intro l
    obtain ⟨x, hx⟩ := hf l
    let xl : FL := (factorLinearEquiv R S F x).1
    refine ⟨xl, ?_⟩
    apply Subtype.ext
    change (f (leftIdempotent R S • x)).1 = l.1
    rw [f.map_smul, hx]
    have hl := left_smul_add_right_smul R S M l.1
    rw [l.property, add_zero] at hl
    exact hl
  obtain ⟨hLeft, hh⟩ :=
    Module.projective_lifting_property fLeft (LinearMap.id : L →ₗ[R] L) hfLeft
  let h : L →ₗ[R × S] F :=
    { toFun := fun l ↦ (hLeft l).1
      map_add' := by intros; simp
      map_smul' := by
        intro a l
        have hin : a • l = a.1 • l := by
          apply Subtype.ext
          exact leftSubmodule_smul_val R S M a l
        change (hLeft (a • l)).1 = a • (hLeft l).1
        rw [hin, hLeft.map_smul]
        exact (leftSubmodule_smul_val R S F a (hLeft l)).symm }
  refine ⟨h, ?_⟩
  ext l
  simpa [fLeft, h] using congrArg Subtype.val (DFunLike.congr_fun hh l)

private theorem product_right_of_right (M : Type w) [AddCommMonoid M] [Module (R × S) M]
    [Module.Projective S (rightSubmodule R S M)] :
    Module.Projective (R × S) (rightSubmodule R S M) := by
  let Q := rightSubmodule R S M
  apply Module.Projective.of_lifting_property''
  intro f hf
  let F := Q →₀ (R × S)
  let FQ := rightSubmodule R S F
  let fRight : FQ →ₗ[S] Q :=
    { toFun := fun x ↦ f x.1
      map_add' := by intros; simp
      map_smul' := by
        intro s x
        apply Subtype.ext
        change (f ((s • x).1)).1 = (s • f x.1).1
        rw [rightModule_smul_val, f.map_smul]
        exact (rightModule_smul_val R S M s (f x.1)).symm }
  have hfRight : Function.Surjective fRight := by
    intro q
    obtain ⟨x, hx⟩ := hf q
    let xq : FQ := (factorLinearEquiv R S F x).2
    refine ⟨xq, ?_⟩
    apply Subtype.ext
    change (f (rightIdempotent R S • x)).1 = q.1
    rw [f.map_smul, hx]
    have hq := left_smul_add_right_smul R S M q.1
    rw [q.property, zero_add] at hq
    exact hq
  obtain ⟨hRight, hh⟩ :=
    Module.projective_lifting_property fRight (LinearMap.id : Q →ₗ[S] Q) hfRight
  let h : Q →ₗ[R × S] F :=
    { toFun := fun q ↦ (hRight q).1
      map_add' := by intros; simp
      map_smul' := by
        intro a q
        have hin : a • q = a.2 • q := by
          apply Subtype.ext
          exact rightSubmodule_smul_val R S M a q
        change (hRight (a • q)).1 = a • (hRight q).1
        rw [hin, hRight.map_smul]
        exact (rightSubmodule_smul_val R S F a (hRight q)).symm }
  refine ⟨h, ?_⟩
  ext q
  simpa [fRight, h] using congrArg Subtype.val (DFunLike.congr_fun hh q)

/-- A module over a product semiring is projective exactly when its two idempotent factors are
projective over the corresponding factors. -/
@[stacks 00JH "projective product semiring module criterion"]
theorem product_iff (M : Type w) [AddCommMonoid M] [Module (R × S) M] :
    Module.Projective (R × S) M ↔
      Module.Projective R (Module.Product.leftSubmodule R S M) ∧
        Module.Projective S (Module.Product.rightSubmodule R S M) := by
  constructor
  · intro hM
    letI : Module.Projective (R × S) M := hM
    exact ⟨left_of_product R S M, right_of_product R S M⟩
  · rintro ⟨hL, hQ⟩
    letI : Module.Projective R (leftSubmodule R S M) := hL
    letI : Module.Projective S (rightSubmodule R S M) := hQ
    letI : Module.Projective (R × S) (leftSubmodule R S M) := product_left_of_left R S M
    letI : Module.Projective (R × S) (rightSubmodule R S M) := product_right_of_right R S M
    letI : Module.Projective (R × S)
        (leftSubmodule R S M × rightSubmodule R S M) := inferInstance
    exact Module.Projective.of_equiv' (factorLinearEquiv R S M).symm

end Module.Projective
