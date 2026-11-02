/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Module.MinimalAxioms
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Global-section scalars on module-sheaf cohomology

Compatible global sections of a sheaf of rings act on the cohomology of any
sheaf of modules through additive scalar endomorphisms of its underlying sheaf.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v w m h u' v'

namespace SheafOfModules.GlobalCohomology

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- The ring of compatible global sections of a sheaf of rings. -/
abbrev sectionsRing (O : Sheaf J RingCat.{w}) : Type (max u w) :=
  RingCat.sectionsSubring O.obj

/-- Evaluation of a compatible global section at an object of the site. -/
def sectionsEval (O : Sheaf J RingCat.{w}) (U : Cᵒᵖ) :
    sectionsRing O →+* O.obj.obj U :=
  (Pi.evalRingHom (fun V ↦ O.obj.obj V) U).comp
    (RingCat.sectionsSubring O.obj).subtype

section Pullback

variable {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
variable (OX : Sheaf J RingCat.{w}) (OY : Sheaf K RingCat.{w})
variable (G : C ⥤ D) (η : G.op ⋙ OY.obj ⟶ OX.obj)

/-- Pulling back a global section along a morphism of ring presheaves gives a
compatible family. -/
theorem sectionsPullback_naturality (s : sectionsRing OY) {U V : Cᵒᵖ} (i : U ⟶ V) :
    OX.obj.map i ((η.app U).hom (sectionsEval OY (G.op.obj U) s)) =
      (η.app V).hom (sectionsEval OY (G.op.obj V) s) := by
  have hs : OY.obj.map (G.op.map i) (sectionsEval OY (G.op.obj U) s) =
      sectionsEval OY (G.op.obj V) s := s.property (G.op.map i)
  calc
    _ = (η.app V).hom
        (OY.obj.map (G.op.map i) (sectionsEval OY (G.op.obj U) s)) :=
      (CategoryTheory.congr_fun (η.naturality i) _).symm
    _ = _ := congrArg (η.app V).hom hs

/-- The homomorphism on global sections induced by a morphism of ring presheaves
over a functor of sites. -/
def sectionsPullback : sectionsRing OY →+* sectionsRing OX :=
  (RingHom.pi (fun U ↦ (η.app U).hom.comp (sectionsEval OY (G.op.obj U)))).codRestrict
    (RingCat.sectionsSubring OX.obj)
    (fun s _ _ i ↦ sectionsPullback_naturality OX OY G η s i)

/-- Evaluation of a pulled-back global section is the component ring map applied
to the original section at the image object. -/
theorem sectionsPullback_apply (s : sectionsRing OY) (U : Cᵒᵖ) :
    sectionsEval OX U (sectionsPullback OX OY G η s) =
      (η.app U).hom (sectionsEval OY (G.op.obj U) s) := rfl

end Pullback

variable (O : Sheaf J RingCat.{w}) (F : SheafOfModules.{m} O)

/-- Pointwise multiplication by a global section commutes with restriction on
the underlying additive presheaf of a module sheaf. -/
theorem scalarEndomorphism_naturality (s : sectionsRing O) {U V : Cᵒᵖ} (i : U ⟶ V) :
    F.val.presheaf.map i ≫
        AddCommGrpCat.ofHom (DistribSMul.toAddMonoidHom (F.val.obj V) (sectionsEval O V s)) =
      AddCommGrpCat.ofHom (DistribSMul.toAddMonoidHom (F.val.obj U) (sectionsEval O U s)) ≫
        F.val.presheaf.map i := by
  ext x
  change F.val.obj U at x
  change sectionsEval O V s • F.val.map i x =
    F.val.map i (sectionsEval O U s • x)
  rw [F.val.map_smul]
  have hs : O.obj.map i (sectionsEval O U s) = sectionsEval O V s := s.property i
  rw [hs]

/-- Multiplication by a compatible global section as an additive sheaf endomorphism. -/
def scalarEndomorphism (s : sectionsRing O) :
    (toSheaf O).obj F ⟶ (toSheaf O).obj F where
  hom :=
    { app := fun U ↦
        AddCommGrpCat.ofHom (DistribSMul.toAddMonoidHom (F.val.obj U) (sectionsEval O U s))
      naturality := fun _ _ i ↦ scalarEndomorphism_naturality O F s i }

variable [HasSheafify J AddCommGrpCat.{m}]
variable [HasExt.{h} (Sheaf J AddCommGrpCat.{m})]

/-- Global sections act on cohomology by the maps induced by additive scalar
endomorphisms of the coefficient sheaf. -/
instance instSMul (q : ℕ) :
    SMul (sectionsRing O) ((Sheaf.functorH J q).obj ((toSheaf O).obj F)) where
  smul s x := (Sheaf.functorH J q).map (scalarEndomorphism O F s) x

/-- The global-section action on cohomology distributes over addition of classes. -/
theorem smul_add (q : ℕ) (s : sectionsRing O)
    (x y : (Sheaf.functorH J q).obj ((toSheaf O).obj F)) :
    s • (x + y) = s • x + s • y := by
  exact map_add ((Sheaf.functorH J q).map (scalarEndomorphism O F s)).hom x y

/-- Addition of global sections acts as addition of their actions on cohomology. -/
theorem add_smul (q : ℕ) (s t : sectionsRing O)
    (x : (Sheaf.functorH J q).obj ((toSheaf O).obj F)) :
    (s + t) • x = s • x + t • x := by
  have h : scalarEndomorphism O F (s + t) =
      scalarEndomorphism O F s + scalarEndomorphism O F t := by
    ext U x
    change F.val.obj U at x
    change sectionsEval O U (s + t) • x =
      sectionsEval O U s • x + sectionsEval O U t • x
    rw [map_add, _root_.add_smul]
  change (Sheaf.functorH J q).map (scalarEndomorphism O F (s + t)) x =
    (Sheaf.functorH J q).map (scalarEndomorphism O F s) x +
      (Sheaf.functorH J q).map (scalarEndomorphism O F t) x
  rw [h, CategoryTheory.Functor.map_add]
  rfl

/-- Multiplication of global sections acts by composition on cohomology. -/
theorem mul_smul (q : ℕ) (s t : sectionsRing O)
    (x : (Sheaf.functorH J q).obj ((toSheaf O).obj F)) :
    (s * t) • x = s • (t • x) := by
  have h : scalarEndomorphism O F (s * t) =
      scalarEndomorphism O F t ≫ scalarEndomorphism O F s := by
    ext U x
    change F.val.obj U at x
    change sectionsEval O U (s * t) • x =
      sectionsEval O U s • (sectionsEval O U t • x)
    rw [map_mul, SemigroupAction.mul_smul]
  change (Sheaf.functorH J q).map (scalarEndomorphism O F (s * t)) x =
    (Sheaf.functorH J q).map (scalarEndomorphism O F s)
      ((Sheaf.functorH J q).map (scalarEndomorphism O F t) x)
  rw [h, CategoryTheory.Functor.map_comp]
  rfl

/-- The unit global section acts as the identity on cohomology. -/
theorem one_smul (q : ℕ) (x : (Sheaf.functorH J q).obj ((toSheaf O).obj F)) :
    (1 : sectionsRing O) • x = x := by
  have h : scalarEndomorphism O F 1 = 𝟙 ((toSheaf O).obj F) := by
    ext U x
    change F.val.obj U at x
    change sectionsEval O U 1 • x = x
    rw [map_one, _root_.one_smul]
  change (Sheaf.functorH J q).map (scalarEndomorphism O F 1) x = x
  rw [h, CategoryTheory.Functor.map_id]
  rfl

/-- Cohomology of a module sheaf is canonically a module over its ring of global
sections. -/
instance instModule (q : ℕ) :
    Module (sectionsRing O) ((Sheaf.functorH J q).obj ((toSheaf O).obj F)) :=
  Module.ofMinimalAxioms (smul_add O F q) (add_smul O F q)
    (mul_smul O F q) (one_smul O F q)

/-- Degree-`q` cohomology of a module sheaf, bundled over the global-section ring. -/
def obj (q : ℕ) : ModuleCat.{h} (sectionsRing O) :=
  ModuleCat.of (sectionsRing O) ((Sheaf.functorH J q).obj ((toSheaf O).obj F))

/-- Scalar multiplication on cohomology is the cohomology map of pointwise
scalar multiplication on the coefficient sheaf. -/
theorem smul_def (q : ℕ) (s : sectionsRing O)
    (x : (Sheaf.functorH J q).obj ((toSheaf O).obj F)) :
    s • x = (Sheaf.functorH J q).map (scalarEndomorphism O F s) x := rfl

end SheafOfModules.GlobalCohomology
