/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Tensor.Bilinear
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.SheafOfTypes

/-!
# Local descent of bilinear maps into a sheaf

This file extends the existing `PresheafOfModules.BilinearMap`.  The input presheaves
need not be sheaves: local preimages are compared on covering equalizer sieves, and
only the target is required to satisfy the actual sheaf condition.

The section data below are image-sieve local preimages followed by amalgamation in
the given target sheaf.  No inverse, tensor stability, or extension existence is
assumed in order to define them.  The remaining `sorry` terms are Prop proof debt.
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u v w

namespace PresheafOfModules.BilinearMap

variable {C : Type u} [Category.{v} C]
variable {R : Cᵒᵖ ⥤ CommRingCat.{w}} {J : GrothendieckTopology C}
variable {P₁ P₂ Q H : PresheafOfModules.{w} (ringPresheaf R)}

/-- Evaluate the original bilinear map at actual local preimages in its first input. -/
private def leftLocalFamily (f : P₁ ⟶ P₂) (b : BilinearMap R P₁ Q H)
    (U : Cᵒᵖ) (p : P₂.obj U) (q : Q.obj U) :
    Presieve.FamilyOfElements (H.presheaf ⋙ forget AddCommGrpCat.{w})
      (Presheaf.imageSieve ((toPresheaf (ringPresheaf R)).map f) p).arrows :=
  fun V a ha =>
    b.app (op V)
      (Presheaf.localPreimage ((toPresheaf (ringPresheaf R)).map f) p a ha)
      (Q.map a.op q)

/-- Equal images of two local lifts give equal target values by local injectivity
and target separatedness.  The source is not assumed separated. -/
private theorem leftLocalFamily_compatible (f : P₁ ⟶ P₂)
    [Presheaf.IsLocallyInjective J ((toPresheaf (ringPresheaf R)).map f)]
    (hH : Presieve.IsSheaf J (H.presheaf ⋙ forget AddCommGrpCat.{w}))
    (b : BilinearMap R P₁ Q H) (U : Cᵒᵖ) (p : P₂.obj U) (q : Q.obj U) :
    (leftLocalFamily f b U p q).Compatible := by
  -- On a common refinement the two lifts have equal f-images.  Restrict to
  -- their covering equalizer sieve, apply b.naturality, then H separatedness.
  sorry

/-- The descended section is the actual amalgamation in the supplied target sheaf. -/
private def leftSection (f : P₁ ⟶ P₂)
    [Presheaf.IsLocallyInjective J ((toPresheaf (ringPresheaf R)).map f)]
    [Presheaf.IsLocallySurjective J ((toPresheaf (ringPresheaf R)).map f)]
    (hH : Presieve.IsSheaf J (H.presheaf ⋙ forget AddCommGrpCat.{w}))
    (b : BilinearMap R P₁ Q H) (U : Cᵒᵖ) (p : P₂.obj U) (q : Q.obj U) : H.obj U :=
  (hH (Presheaf.imageSieve ((toPresheaf (ringPresheaf R)).map f) p)
    (Presheaf.imageSieve_mem J ((toPresheaf (ringPresheaf R)).map f) p)).amalgamate
      (leftLocalFamily f b U p q)
      (leftLocalFamily_compatible (J := J) f hH b U p q)

section LeftLaws

-- Every needed local condition below is an explicit declaration binder.

/-- Evaluation may use any actual local lift, not just the selected local preimage. -/
private theorem leftSection_restrict
    (f : P₁ ⟶ P₂)
    [Presheaf.IsLocallyInjective J ((toPresheaf (ringPresheaf R)).map f)]
    [Presheaf.IsLocallySurjective J ((toPresheaf (ringPresheaf R)).map f)]
    (hH : Presieve.IsSheaf J (H.presheaf ⋙ forget AddCommGrpCat.{w}))
    (b : BilinearMap R P₁ Q H) (U : Cᵒᵖ) (p : P₂.obj U) (q : Q.obj U)
    {V : C} (a : V ⟶ U.unop) (x : P₁.obj (op V))
    (hx : f.app (op V) x = P₂.map a.op p) :
    H.map a.op (leftSection f hH b U p q) = b.app (op V) x (Q.map a.op q) := by
  -- valid_glue evaluates the chosen lift; the covering equalizer sieve and
  -- H separatedness replace that lift by x.
  sorry

private theorem leftSection_add_left
    (f : P₁ ⟶ P₂)
    [Presheaf.IsLocallyInjective J ((toPresheaf (ringPresheaf R)).map f)]
    [Presheaf.IsLocallySurjective J ((toPresheaf (ringPresheaf R)).map f)]
    (hH : Presieve.IsSheaf J (H.presheaf ⋙ forget AddCommGrpCat.{w}))
    (b : BilinearMap R P₁ Q H) (U : Cᵒᵖ) (p p' : P₂.obj U) (q : Q.obj U) :
    leftSection f hH b U (p + p') q =
      leftSection f hH b U p q + leftSection f hH b U p' q := by
  -- Intersect the two image covers and use the sum of actual lifts.
  sorry

private theorem leftSection_smul_left
    (f : P₁ ⟶ P₂)
    [Presheaf.IsLocallyInjective J ((toPresheaf (ringPresheaf R)).map f)]
    [Presheaf.IsLocallySurjective J ((toPresheaf (ringPresheaf R)).map f)]
    (hH : Presieve.IsSheaf J (H.presheaf ⋙ forget AddCommGrpCat.{w}))
    (b : BilinearMap R P₁ Q H) (U : Cᵒᵖ) (r : R.obj U)
    (p : P₂.obj U) (q : Q.obj U) :
    leftSection f hH b U (r • p) q = r • leftSection f hH b U p q := by
  -- On the image cover use the restricted coefficient times a lift of p.
  sorry

private theorem leftSection_add_right
    (f : P₁ ⟶ P₂)
    [Presheaf.IsLocallyInjective J ((toPresheaf (ringPresheaf R)).map f)]
    [Presheaf.IsLocallySurjective J ((toPresheaf (ringPresheaf R)).map f)]
    (hH : Presieve.IsSheaf J (H.presheaf ⋙ forget AddCommGrpCat.{w}))
    (b : BilinearMap R P₁ Q H) (U : Cᵒᵖ) (p : P₂.obj U) (q q' : Q.obj U) :
    leftSection f hH b U p (q + q') =
      leftSection f hH b U p q + leftSection f hH b U p q' := by
  -- The same image cover of p works for both second-input sections.
  sorry

private theorem leftSection_smul_right
    (f : P₁ ⟶ P₂)
    [Presheaf.IsLocallyInjective J ((toPresheaf (ringPresheaf R)).map f)]
    [Presheaf.IsLocallySurjective J ((toPresheaf (ringPresheaf R)).map f)]
    (hH : Presieve.IsSheaf J (H.presheaf ⋙ forget AddCommGrpCat.{w}))
    (b : BilinearMap R P₁ Q H) (U : Cᵒᵖ) (r : R.obj U)
    (p : P₂.obj U) (q : Q.obj U) :
    leftSection f hH b U p (r • q) = r • leftSection f hH b U p q := by
  -- Restrictions of Q are semilinear over the actual restricted coefficient.
  sorry

private theorem leftSection_naturality
    (f : P₁ ⟶ P₂)
    [Presheaf.IsLocallyInjective J ((toPresheaf (ringPresheaf R)).map f)]
    [Presheaf.IsLocallySurjective J ((toPresheaf (ringPresheaf R)).map f)]
    (hH : Presieve.IsSheaf J (H.presheaf ⋙ forget AddCommGrpCat.{w}))
    (b : BilinearMap R P₁ Q H) {U V : Cᵒᵖ} (i : U ⟶ V)
    (p : P₂.obj U) (q : Q.obj U) :
    H.map i (leftSection f hH b U p q) =
      leftSection f hH b V (P₂.map i p) (Q.map i q) := by
  -- Compare on the image cover of the restricted p using leftSection_restrict.
  sorry

/-- Extend a bilinear map in its first variable along a locally bijective map.
The target's sheaf property is actual input; neither source is assumed a sheaf. -/
def descendLeft
    (f : P₁ ⟶ P₂)
    [Presheaf.IsLocallyInjective J ((toPresheaf (ringPresheaf R)).map f)]
    [Presheaf.IsLocallySurjective J ((toPresheaf (ringPresheaf R)).map f)]
    (hH : Presieve.IsSheaf J (H.presheaf ⋙ forget AddCommGrpCat.{w}))
    (b : BilinearMap R P₁ Q H) : BilinearMap R P₂ Q H where
  app U :=
    { toFun := fun p =>
        { toFun := fun q =>
            (hH (Presheaf.imageSieve ((toPresheaf (ringPresheaf R)).map f) p)
              (Presheaf.imageSieve_mem J ((toPresheaf (ringPresheaf R)).map f) p)).amalgamate
                (fun V a ha =>
                  b.app (op V)
                    (Presheaf.localPreimage
                      ((toPresheaf (ringPresheaf R)).map f) p a ha)
                    (Q.map a.op q))
                (by exact leftLocalFamily_compatible (J := J) f hH b U p q)
          map_add' := by
            intro q q'
            exact leftSection_add_right f hH b U p q q'
          map_smul' := by
            intro r q
            exact leftSection_smul_right f hH b U r p q }
      map_add' := by
        intro p p'
        ext q
        exact leftSection_add_left f hH b U p p' q
      map_smul' := by
        intro r p
        ext q
        exact leftSection_smul_left f hH b U r p q }
  naturality i p q := by
    exact leftSection_naturality f hH b i p q

/-- Descent agrees with the original map on every actual preimage. -/
@[simp]
theorem descendLeft_app
    (f : P₁ ⟶ P₂)
    [Presheaf.IsLocallyInjective J ((toPresheaf (ringPresheaf R)).map f)]
    [Presheaf.IsLocallySurjective J ((toPresheaf (ringPresheaf R)).map f)]
    (hH : Presieve.IsSheaf J (H.presheaf ⋙ forget AddCommGrpCat.{w}))
    (b : BilinearMap R P₁ Q H) (U : Cᵒᵖ) (x : P₁.obj U) (q : Q.obj U) :
    (descendLeft f hH b).app U (f.app U x) q = b.app U x q := by
  -- leftSection_restrict at the identity arrow.
  sorry

/-- The extension into a sheaf target is unique. -/
theorem descendLeft_unique
    (f : P₁ ⟶ P₂)
    [Presheaf.IsLocallyInjective J ((toPresheaf (ringPresheaf R)).map f)]
    [Presheaf.IsLocallySurjective J ((toPresheaf (ringPresheaf R)).map f)]
    (hH : Presieve.IsSheaf J (H.presheaf ⋙ forget AddCommGrpCat.{w}))
    (b : BilinearMap R P₁ Q H) (c : BilinearMap R P₂ Q H)
    (hc : ∀ (U : Cᵒᵖ) (x : P₁.obj U) (q : Q.obj U),
      c.app U (f.app U x) q = b.app U x q) :
    c = descendLeft f hH b := by
  -- Compare on the image cover of p and use target separatedness, then ext.
  sorry

end LeftLaws


section Right

variable {P Q₁ Q₂ : PresheafOfModules.{w} (ringPresheaf R)}
-- Explicit conditions are retained even in deferred Prop proofs.

/-- Extend the second variable using the same actual local-preimage/gluing data. -/
def descendRight
    (g : Q₁ ⟶ Q₂)
    [Presheaf.IsLocallyInjective J ((toPresheaf (ringPresheaf R)).map g)]
    [Presheaf.IsLocallySurjective J ((toPresheaf (ringPresheaf R)).map g)]
    (hH : Presieve.IsSheaf J (H.presheaf ⋙ forget AddCommGrpCat.{w}))
    (b : BilinearMap R P Q₁ H) : BilinearMap R P Q₂ H :=
  let swapped : BilinearMap R Q₁ P H :=
    { app U := (b.app U).flip
      naturality i y x := by exact b.naturality i x y }
  let extended := descendLeft g hH swapped
  { app U := (extended.app U).flip
    naturality i p q := by exact extended.naturality i q p }

/-- Second-variable descent agrees with the original map on actual preimages. -/
@[simp]
theorem descendRight_app
    (g : Q₁ ⟶ Q₂)
    [Presheaf.IsLocallyInjective J ((toPresheaf (ringPresheaf R)).map g)]
    [Presheaf.IsLocallySurjective J ((toPresheaf (ringPresheaf R)).map g)]
    (hH : Presieve.IsSheaf J (H.presheaf ⋙ forget AddCommGrpCat.{w}))
    (b : BilinearMap R P Q₁ H) (U : Cᵒᵖ) (p : P.obj U) (y : Q₁.obj U) :
    (descendRight g hH b).app U p (g.app U y) = b.app U p y := by
  let swapped : BilinearMap R Q₁ P H :=
    { app U := (b.app U).flip
      naturality i y x := by exact b.naturality i x y }
  change (descendLeft g hH swapped).app U (g.app U y) p = b.app U p y
  exact descendLeft_app g hH swapped U y p

/-- Second-variable extension into the sheaf target is unique. -/
theorem descendRight_unique
    (g : Q₁ ⟶ Q₂)
    [Presheaf.IsLocallyInjective J ((toPresheaf (ringPresheaf R)).map g)]
    [Presheaf.IsLocallySurjective J ((toPresheaf (ringPresheaf R)).map g)]
    (hH : Presieve.IsSheaf J (H.presheaf ⋙ forget AddCommGrpCat.{w}))
    (b : BilinearMap R P Q₁ H) (c : BilinearMap R P Q₂ H)
    (hc : ∀ (U : Cᵒᵖ) (p : P.obj U) (y : Q₁.obj U),
      c.app U p (g.app U y) = b.app U p y) :
    c = descendRight g hH b := by
  -- Apply first-variable uniqueness after the actual input swap and the existing ext lemma.
  sorry

end Right

end PresheafOfModules.BilinearMap
