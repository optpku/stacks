/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.Tactic.CrossRefAttribute

/-!
# Exactness of sheaves of abelian groups

This leaf relates categorical kernels, cokernels, monomorphisms, epimorphisms, and exact short
complexes of abelian sheaves to the corresponding local or sectionwise descriptions.  The
categorical `ShortComplex.Exact` interface remains the primary owner; local lifting is exposed as
a reusable predicate and an `iff`, rather than being buried in a chapter proof.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

namespace Sheaf

variable {F G : Sheaf J AddCommGrpCat.{w}} (φ : F ⟶ G)

/-- Lemma 18.3.1 (03CN) (3): a morphism of abelian sheaves is monic exactly when
all of its maps on sections are injective. -/
@[stacks 03CN "sectionwise injectivity"]
theorem mono_iff_app_injective :
    Mono φ ↔ ∀ U : C, Function.Injective (φ.hom.app (op U)) := sorry

variable [HasSheafify J AddCommGrpCat.{w}]

/-- Lemma 18.3.1 (03CN) (4): the cokernel sheaf is the sheafification of the
cokernel of the underlying abelian-presheaf morphism. -/
@[stacks 03CN "cokernel"]
noncomputable def cokernelSheafificationIso :
    cokernel φ ≅
      (presheafToSheaf J AddCommGrpCat.{w}).obj
        (cokernel ((sheafToPresheaf J AddCommGrpCat.{w}).map φ)) :=
  (cokernel.mapIso φ
      ((presheafToSheaf J AddCommGrpCat.{w}).map
        ((sheafToPresheaf J AddCommGrpCat.{w}).map φ))
      ((sheafificationNatIso J AddCommGrpCat.{w}).app F)
      ((sheafificationNatIso J AddCommGrpCat.{w}).app G)
      ((sheafificationNatIso J AddCommGrpCat.{w}).hom.naturality φ)) ≪≫
    (PreservesCokernel.iso (presheafToSheaf J AddCommGrpCat.{w})
      ((sheafToPresheaf J AddCommGrpCat.{w}).map φ)).symm

end Sheaf

namespace ShortComplex

/-- The sectionwise local lifting condition for a short complex of abelian sheaves. -/
@[stacks 03CN "local lifting condition"]
def IsSectionwiseLocallyExact
    (S : ShortComplex (Sheaf J AddCommGrpCat.{w})) : Prop :=
  ∀ (U : C) (s : S.X₂.obj.obj (Opposite.op U)),
    S.g.hom.app (Opposite.op U) s = 0 →
    ∃ T : J.Cover U, ∀ I : T.Arrow,
      ∃ t : S.X₁.obj.obj (Opposite.op I.Y),
        S.f.hom.app (Opposite.op I.Y) t = S.X₂.obj.map I.f.op s

variable [HasSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [J.HasSheafCompose (forget AddCommGrpCat.{w})]

/-- Exactness is equivalent to local surjectivity of the canonical morphism to the kernel. -/
@[stacks 03CN "kernel-lift criterion"]
theorem exact_iff_isLocallySurjective_kernel_lift
    (S : ShortComplex (Sheaf J AddCommGrpCat.{w})) :
    S.Exact ↔ Sheaf.IsLocallySurjective (kernel.lift S.g S.f S.zero) := sorry

/-- Lemma 18.3.1 (03CN) (6): a short complex of abelian sheaves is exact exactly when it satisfies
the sectionwise local lifting condition. -/
@[stacks 03CN "local exactness"]
theorem exact_iff_locally_surjective_sections
    (S : ShortComplex (Sheaf J AddCommGrpCat.{w})) :
    S.Exact ↔ S.IsSectionwiseLocallyExact := sorry

end ShortComplex

end CategoryTheory
