/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Exact
public import ReasLib.Algebra.Module.Product

/-!
# Modules over Product Rings

This file provides the two idempotent factors of a module over a product ring.  It is independent
of Grothendieck groups, finite-generation hypotheses, and projectivity, so it can be used by any
later construction on modules over `R × S`.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v w

namespace CategoryTheory.ModuleCat.Product

variable (R : Type u) (S : Type v) [Ring R] [Ring S]

/-- The heterogeneous product category instance for module categories over rings in independent
universes.  This keeps `CategoryTheory.prod'` from being shadowed by the same-universe
`CategoryTheory.uniformProd` convenience instance. -/
-- Local instance justification (instance diamond): choose the heterogeneous product category.
local instance heterogeneousModuleCategory :
    Category.{w} (ModuleCat.{w} R × ModuleCat.{w} S) :=
  CategoryTheory.prod' (ModuleCat.{w} R) (ModuleCat.{w} S)

/-- The left factor of a bundled `(R × S)`-module, viewed as a bundled `R`-module. -/
@[stacks 00JH "bundled product ring left factor"]
def left (M : ModuleCat.{w} (R × S)) : ModuleCat.{w} R :=
  @ModuleCat.of R _ (Module.Product.leftSubmodule R S M) _
    (Module.Product.leftModule R S M)

/-- The right factor of a bundled `(R × S)`-module, viewed as a bundled `S`-module. -/
@[stacks 00JH "bundled product ring right factor"]
def right (M : ModuleCat.{w} (R × S)) : ModuleCat.{w} S :=
  @ModuleCat.of S _ (Module.Product.rightSubmodule R S M) _
    (Module.Product.rightModule R S M)

/-- The canonical `R`-module structure on a bundled left factor.  This named instance keeps the
structure available without unfolding the bundled `left` definition. -/
@[stacks 00JH "bundled product ring left factor module structure"]
instance leftModule (M : ModuleCat.{w} (R × S)) : Module R (left R S M) :=
  Module.Product.leftModule R S M

/-- The canonical `S`-module structure on a bundled right factor.  This named instance keeps the
structure available without unfolding the bundled `right` definition. -/
@[stacks 00JH "bundled product ring right factor module structure"]
instance rightModule (M : ModuleCat.{w} (R × S)) : Module S (right R S M) :=
  Module.Product.rightModule R S M

/-- The map induced on left factors by a morphism of `(R × S)`-modules. -/
@[stacks 00JH "product ring left factor map"]
def leftMap {M N : ModuleCat.{w} (R × S)} (f : M ⟶ N) :
    left R S M ⟶ left R S N :=
  ModuleCat.ofHom
    { toFun := fun m ↦ ⟨f.hom m.1, by
        change Module.Product.rightIdempotent R S • f.hom m.1 = 0
        rw [← f.hom.map_smul, m.property, map_zero]⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        exact f.hom.map_add x.1 y.1
      map_smul' := by
        intro r x
        apply Subtype.ext
        change f.hom (((r, (0 : S)) : R × S) • x.1) =
          ((r, (0 : S)) : R × S) • f.hom x.1
        exact f.hom.map_smul ((r, 0) : R × S) x.1 }

/-- The map induced on right factors by a morphism of `(R × S)`-modules. -/
@[stacks 00JH "product ring right factor map"]
def rightMap {M N : ModuleCat.{w} (R × S)} (f : M ⟶ N) :
    right R S M ⟶ right R S N :=
  ModuleCat.ofHom
    { toFun := fun m ↦ ⟨f.hom m.1, by
        change Module.Product.leftIdempotent R S • f.hom m.1 = 0
        rw [← f.hom.map_smul, m.property, map_zero]⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        exact f.hom.map_add x.1 y.1
      map_smul' := by
        intro s x
        apply Subtype.ext
        change f.hom ((((0 : R), s) : R × S) • x.1) =
          (((0 : R), s) : R × S) • f.hom x.1
        exact f.hom.map_smul ((0, s) : R × S) x.1 }

/-- The left-factor map is the original module map on underlying elements. -/
@[simp]
theorem leftMap_apply {M N : ModuleCat.{w} (R × S)} (f : M ⟶ N) (m : left R S M) :
    (leftMap R S f m).1 = f.hom m.1 := rfl

/-- The right-factor map is the original module map on underlying elements. -/
@[simp]
theorem rightMap_apply {M N : ModuleCat.{w} (R × S)} (f : M ⟶ N) (m : right R S M) :
    (rightMap R S f m).1 = f.hom m.1 := rfl

/-- The functor taking an `(R × S)`-module to its left idempotent factor. -/
@[stacks 00JH "product ring left factor functor"]
def leftFunctor : ModuleCat.{w} (R × S) ⥤ ModuleCat.{w} R where
  obj M := left R S M
  map f := leftMap R S f
  map_id := by
    intro M
    ext m
    rfl
  map_comp := by
    intro M N P f g
    ext m
    rfl

/-- The functor taking an `(R × S)`-module to its right idempotent factor. -/
@[stacks 00JH "product ring right factor functor"]
def rightFunctor : ModuleCat.{w} (R × S) ⥤ ModuleCat.{w} S where
  obj M := right R S M
  map f := rightMap R S f
  map_id := by
    intro M
    ext m
    rfl
  map_comp := by
    intro M N P f g
    ext m
    rfl

/-- The left-factor functor is additive. -/
@[stacks 00JH "product ring left factor additive functor"]
instance leftFunctor_additive : (leftFunctor R S).Additive where
  map_add := by
    intro M N f g
    ext m
    rfl

/-- The right-factor functor is additive. -/
@[stacks 00JH "product ring right factor additive functor"]
instance rightFunctor_additive : (rightFunctor R S).Additive where
  map_add := by
    intro M N f g
    ext m
    rfl

/-- Taking the left idempotent factor preserves exact short complexes. -/
@[stacks 00JH "product ring left factor preserves exact complexes"]
theorem leftFunctor_map_exact (T : ShortComplex (ModuleCat.{w} (R × S))) (hT : T.Exact) :
    (T.map (leftFunctor R S)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff] at hT ⊢
  intro x hx
  obtain ⟨y, hy⟩ := hT x.1 (congrArg Subtype.val hx)
  refine ⟨⟨Module.Product.leftIdempotent R S • y, ?_⟩, ?_⟩
  · change Module.Product.rightIdempotent R S •
      (Module.Product.leftIdempotent R S • y) = 0
    rw [smul_smul, Module.Product.rightIdempotent_mul_leftIdempotent, zero_smul]
  · apply Subtype.ext
    change T.f (Module.Product.leftIdempotent R S • y) = x.1
    rw [T.f.hom.map_smul, hy]
    simpa only [Module.Product.leftIdempotent, one_smul] using
      Module.Product.leftSubmodule_smul_val R S T.X₂
        (Module.Product.leftIdempotent R S) x

/-- Taking the right idempotent factor preserves exact short complexes. -/
@[stacks 00JH "product ring right factor preserves exact complexes"]
theorem rightFunctor_map_exact (T : ShortComplex (ModuleCat.{w} (R × S))) (hT : T.Exact) :
    (T.map (rightFunctor R S)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff] at hT ⊢
  intro x hx
  obtain ⟨y, hy⟩ := hT x.1 (congrArg Subtype.val hx)
  refine ⟨⟨Module.Product.rightIdempotent R S • y, ?_⟩, ?_⟩
  · change Module.Product.leftIdempotent R S •
      (Module.Product.rightIdempotent R S • y) = 0
    rw [smul_smul, Module.Product.leftIdempotent_mul_rightIdempotent, zero_smul]
  · apply Subtype.ext
    change T.f (Module.Product.rightIdempotent R S • y) = x.1
    rw [T.f.hom.map_smul, hy]
    simpa only [Module.Product.rightIdempotent, one_smul] using
      Module.Product.rightSubmodule_smul_val R S T.X₂
        (Module.Product.rightIdempotent R S) x

/-- The left-factor functor is exact. -/
@[stacks 00JH "product ring left factor exact"]
theorem leftFunctor_exact :
    exactFunctor (ModuleCat.{w} (R × S)) (ModuleCat.{w} R) (leftFunctor R S) := by
  exact ((Functor.exact_tfae (leftFunctor R S)).out 1 3).mp (leftFunctor_map_exact R S)

/-- The left-factor functor bundled as an exact functor. -/
@[stacks 00JH "product ring left exact factor functor"]
def leftExactFunctor : ModuleCat.{w} (R × S) ⥤ₑ ModuleCat.{w} R :=
  ⟨leftFunctor R S, leftFunctor_exact R S⟩

/-- The right-factor functor is exact. -/
@[stacks 00JH "product ring right factor exact"]
theorem rightFunctor_exact :
    exactFunctor (ModuleCat.{w} (R × S)) (ModuleCat.{w} S) (rightFunctor R S) := by
  exact ((Functor.exact_tfae (rightFunctor R S)).out 1 3).mp (rightFunctor_map_exact R S)

/-- The right-factor functor bundled as an exact functor. -/
@[stacks 00JH "product ring right exact factor functor"]
def rightExactFunctor : ModuleCat.{w} (R × S) ⥤ₑ ModuleCat.{w} S :=
  ⟨rightFunctor R S, rightFunctor_exact R S⟩

/-- The functor sending a product-ring module to its pair of idempotent factors. -/
@[stacks 00JH "product ring factor functor"]
def factor : ModuleCat.{w} (R × S) ⥤ ModuleCat.{w} R × ModuleCat.{w} S :=
  (leftFunctor R S).prod' (rightFunctor R S)

/-- Combine an `R`-module and an `S`-module into a module over `R × S`. -/
@[stacks 00JH "product ring combined module"]
def combineObj (M : ModuleCat.{w} R) (N : ModuleCat.{w} S) : ModuleCat.{w} (R × S) :=
  @ModuleCat.of (R × S) _ (M × N) _ (Module.Product.componentwise R S M N)

/-- The morphism of product-ring modules induced by a pair of module morphisms. -/
@[stacks 00JH "product ring combined module map"]
def combineMap {M M' : ModuleCat.{w} R} {N N' : ModuleCat.{w} S}
    (f : M ⟶ M') (g : N ⟶ N') : combineObj R S M N ⟶ combineObj R S M' N' :=
  -- Local instance justification (defeq pin): use the componentwise action of the source.
  letI : Module (R × S) (M × N) := Module.Product.componentwise R S M N
  -- Local instance justification (defeq pin): use the componentwise action of the target.
  letI : Module (R × S) (M' × N') := Module.Product.componentwise R S M' N'
  ModuleCat.ofHom
    { toFun := fun x ↦ (f.hom x.1, g.hom x.2)
      map_add' := by
        intro x y
        apply Prod.ext
        · exact f.hom.map_add x.1 y.1
        · exact g.hom.map_add x.2 y.2
      map_smul' := by
        intro a x
        apply Prod.ext
        · exact f.hom.map_smul a.1 x.1
        · exact g.hom.map_smul a.2 x.2 }

/-- A combined module map acts componentwise on the underlying product. -/
@[simp]
theorem combineMap_apply {M M' : ModuleCat.{w} R} {N N' : ModuleCat.{w} S}
    (f : M ⟶ M') (g : N ⟶ N') (x : combineObj R S M N) :
    combineMap R S f g x = (f.hom x.1, g.hom x.2) := rfl

/-- The functor combining modules over the two factors into a module over their product ring. -/
@[stacks 00JH "product ring combination functor"]
def combine : ModuleCat.{w} R × ModuleCat.{w} S ⥤ ModuleCat.{w} (R × S) where
  obj X := combineObj R S X.1 X.2
  map f := combineMap R S f.1 f.2
  map_id := by
    intro X
    ext x <;> rfl
  map_comp := by
    intro X Y Z f g
    ext x <;> rfl

/-- The functor embedding `R`-modules as `(R × S)`-modules through the first projection. -/
@[stacks 00JH "product ring left embedding functor"]
def leftEmbed : ModuleCat.{w} R ⥤ ModuleCat.{w} (R × S) :=
  ModuleCat.restrictScalars (RingHom.fst R S)

/-- The first-projection embedding is exact. -/
@[stacks 00JH "product ring left embedding exact"]
def leftEmbedExact : ModuleCat.{w} R ⥤ₑ ModuleCat.{w} (R × S) :=
  ⟨leftEmbed R S, ModuleCat.restrictScalars_exact (RingHom.fst R S)⟩

/-- The functor embedding `S`-modules as `(R × S)`-modules through the second projection. -/
@[stacks 00JH "product ring right embedding functor"]
def rightEmbed : ModuleCat.{w} S ⥤ ModuleCat.{w} (R × S) :=
  ModuleCat.restrictScalars (RingHom.snd R S)

/-- The second-projection embedding is exact. -/
@[stacks 00JH "product ring right embedding exact"]
def rightEmbedExact : ModuleCat.{w} S ⥤ₑ ModuleCat.{w} (R × S) :=
  ⟨rightEmbed R S, ModuleCat.restrictScalars_exact (RingHom.snd R S)⟩

namespace LeftEmbed

/-- The left factor of a module embedded through the first projection is the original module. -/
@[stacks 00JH "product ring left embedding left factor"]
def leftIso (M : ModuleCat.{w} R) :
    left R S ((leftEmbed R S).obj M) ≅ M :=
  LinearEquiv.toModuleIso
    { toFun := fun x ↦ x.1
      invFun := fun m ↦ ⟨m, by
        change (0 : R) • m = 0
        simp⟩
      left_inv := fun _ ↦ Subtype.ext rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }

/-- The right factor of a module embedded through the first projection is zero. -/
@[stacks 00JH "product ring left embedding right factor"]
theorem right_subsingleton (M : ModuleCat.{w} R) :
    Subsingleton (right R S ((leftEmbed R S).obj M)) := by
  constructor
  intro x y
  apply Subtype.ext
  have hx := x.property
  have hy := y.property
  change @SMul.smul R M M.isModule.toSMul (1 : R) x.1 = 0 at hx
  change @SMul.smul R M M.isModule.toSMul (1 : R) y.1 = 0 at hy
  have hx1 : @SMul.smul R M M.isModule.toSMul (1 : R) x.1 = x.1 := by
    exact M.isModule.one_smul x.1
  have hy1 : @SMul.smul R M M.isModule.toSMul (1 : R) y.1 = y.1 := by
    exact M.isModule.one_smul y.1
  have hx0 : (x.1 : M) = 0 := hx1.symm.trans hx
  have hy0 : (y.1 : M) = 0 := hy1.symm.trans hy
  exact hx0.trans hy0.symm

end LeftEmbed

namespace RightEmbed

/-- The right factor of a module embedded through the second projection is the original module. -/
@[stacks 00JH "product ring right embedding right factor"]
def rightIso (M : ModuleCat.{w} S) :
    right R S ((rightEmbed R S).obj M) ≅ M :=
  LinearEquiv.toModuleIso
    { toFun := fun x ↦ x.1
      invFun := fun m ↦ ⟨m, by
        change (0 : S) • m = 0
        simp⟩
      left_inv := fun _ ↦ Subtype.ext rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }

/-- The left factor of a module embedded through the second projection is zero. -/
@[stacks 00JH "product ring right embedding left factor"]
theorem left_subsingleton (M : ModuleCat.{w} S) :
    Subsingleton (left R S ((rightEmbed R S).obj M)) := by
  constructor
  intro x y
  apply Subtype.ext
  have hx := x.property
  have hy := y.property
  change @SMul.smul S M M.isModule.toSMul (1 : S) x.1 = 0 at hx
  change @SMul.smul S M M.isModule.toSMul (1 : S) y.1 = 0 at hy
  have hx1 : @SMul.smul S M M.isModule.toSMul (1 : S) x.1 = x.1 := by
    exact M.isModule.one_smul x.1
  have hy1 : @SMul.smul S M M.isModule.toSMul (1 : S) y.1 = y.1 := by
    exact M.isModule.one_smul y.1
  have hx0 : (x.1 : M) = 0 := hx1.symm.trans hx
  have hy0 : (y.1 : M) = 0 := hy1.symm.trans hy
  exact hx0.trans hy0.symm

end RightEmbed

/-- A product-ring module is isomorphic to the combination of its two idempotent factors. -/
@[stacks 00JH "product ring factor combination isomorphism"]
def factorCombineIso (M : ModuleCat.{w} (R × S)) :
    M ≅ combineObj R S (left R S M) (right R S M) :=
  -- Local instance justification (defeq pin): match the bundled combination codomain.
  letI : Module (R × S) (left R S M × right R S M) :=
    Module.Product.componentwise R S (left R S M) (right R S M)
  let e : M ≃ₗ[R × S] (left R S M × right R S M) :=
    Module.Product.factorComponentwiseLinearEquiv R S M
  { hom := ModuleCat.ofHom e.toLinearMap
    inv := ModuleCat.ofHom e.symm.toLinearMap
    hom_inv_id := by
      ext m
      exact e.left_inv m
    inv_hom_id := by
      ext x
      exact e.right_inv x }

/-- The left component of the factor-combination isomorphism is multiplication by `(1, 0)`. -/
@[simp]
theorem factorCombineIso_hom_left (M : ModuleCat.{w} (R × S)) (m : M) :
    ((factorCombineIso R S M).hom m).1.1 = Module.Product.leftIdempotent R S • m := rfl

/-- The right component of the factor-combination isomorphism is multiplication by `(0, 1)`. -/
@[simp]
theorem factorCombineIso_hom_right (M : ModuleCat.{w} (R × S)) (m : M) :
    ((factorCombineIso R S M).hom m).2.1 = Module.Product.rightIdempotent R S • m := rfl

/-- The inverse factor-combination isomorphism adds the two factor elements. -/
@[simp]
theorem factorCombineIso_inv_apply (M : ModuleCat.{w} (R × S))
    (x : combineObj R S (left R S M) (right R S M)) :
    (factorCombineIso R S M).inv x = x.1.1 + x.2.1 := rfl

/-- The left factor of a combined module is canonically the original `R`-module. -/
@[stacks 00JH "product ring left combined factor isomorphism"]
def leftCombineIso (M : ModuleCat.{w} R) (N : ModuleCat.{w} S) :
    left R S (combineObj R S M N) ≅ M :=
  LinearEquiv.toModuleIso
    { toFun := fun x ↦ x.1.1
      invFun := fun m ↦ ⟨(m, 0), by
        change (((0 : R) • m), ((1 : S) • (0 : N))) = 0
        simp⟩
      left_inv := by
        intro x
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · have hx := congrArg (fun p ↦ p.2) x.property
          change (1 : S) • x.1.2 = 0 at hx
          simpa using hx.symm
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }

/-- The right factor of a combined module is canonically the original `S`-module. -/
@[stacks 00JH "product ring right combined factor isomorphism"]
def rightCombineIso (M : ModuleCat.{w} R) (N : ModuleCat.{w} S) :
    right R S (combineObj R S M N) ≅ N :=
  LinearEquiv.toModuleIso
    { toFun := fun x ↦ x.1.2
      invFun := fun n ↦ ⟨(0, n), by
        change (((1 : R) • (0 : M)), ((0 : S) • n)) = 0
        simp⟩
      left_inv := by
        intro x
        apply Subtype.ext
        apply Prod.ext
        · have hx := congrArg (fun p ↦ p.1) x.property
          change (1 : R) • x.1.1 = 0 at hx
          simpa using hx.symm
        · rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }

/-- Combining a pair of modules and then factoring it is canonically isomorphic to the original
pair. -/
@[stacks 00JH "product ring combination factor isomorphism"]
def combineFactorIso (X : ModuleCat.{w} R × ModuleCat.{w} S) :
    (combine R S ⋙ factor R S).obj X ≅ X :=
  Iso.prod (leftCombineIso R S X.1 X.2) (rightCombineIso R S X.1 X.2) ≪≫ prod.etaIso X

/-- The unit isomorphism for the product-ring module equivalence. -/
@[stacks 00JH "product ring module equivalence unit"]
def unitIso : 𝟭 (ModuleCat.{w} (R × S)) ≅ factor R S ⋙ combine R S :=
  NatIso.ofComponents (factorCombineIso R S) (by
    intro M N f
    ext m
    apply Prod.ext
    · apply Subtype.ext
      change Module.Product.leftIdempotent R S • f.hom m =
        f.hom (Module.Product.leftIdempotent R S • m)
      exact (f.hom.map_smul (Module.Product.leftIdempotent R S) m).symm
    · apply Subtype.ext
      change Module.Product.rightIdempotent R S • f.hom m =
        f.hom (Module.Product.rightIdempotent R S • m)
      exact (f.hom.map_smul (Module.Product.rightIdempotent R S) m).symm)

/-- The counit isomorphism for the product-ring module equivalence. -/
@[stacks 00JH "product ring module equivalence counit"]
def counitIso : combine R S ⋙ factor R S ≅ 𝟭 (ModuleCat.{w} R × ModuleCat.{w} S) :=
  NatIso.ofComponents (combineFactorIso R S) (by
    intro X Y f
    apply Prod.ext
    · ext x
      rfl
    · ext x
      rfl)

/-- The canonical equivalence between modules over `R × S` and pairs of modules over `R` and
`S`. -/
@[stacks 00JH "product ring module category equivalence"]
def equivalence : ModuleCat.{w} (R × S) ≌ ModuleCat.{w} R × ModuleCat.{w} S :=
  Equivalence.mk (factor R S) (combine R S) (unitIso R S) (counitIso R S)

/-- The idempotent-factor functor is an equivalence of module categories. -/
@[stacks 00JH "product ring factor functor equivalence"]
instance factor_isEquivalence : (factor R S).IsEquivalence :=
  (equivalence R S).isEquivalence_functor

/-- The product-module combination functor is an equivalence of module categories. -/
@[stacks 00JH "product ring combination functor equivalence"]
instance combine_isEquivalence : (combine R S).IsEquivalence :=
  (equivalence R S).isEquivalence_inverse

end CategoryTheory.ModuleCat.Product
