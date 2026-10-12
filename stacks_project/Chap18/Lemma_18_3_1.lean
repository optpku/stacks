/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Exactness
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {F G : Sheaf J AddCommGrpCat.{max u v}} (φ : F ⟶ G)

/- Lemma 18.3.1 (03CN) (1): abelian sheaves form an abelian category. -/
@[stacks 03CN "abelian category"]
#check (inferInstance : Abelian (Sheaf J AddCommGrpCat.{max u v}))

/- Lemma 18.3.1 (03CN) (2): kernels of abelian sheaves are computed sectionwise. -/
@[stacks 03CN "kernels"]
#check (PreservesKernel.iso
    (sheafToPresheaf J AddCommGrpCat.{max u v}) φ :
  (sheafToPresheaf J AddCommGrpCat.{max u v}).obj (kernel φ) ≅
    kernel ((sheafToPresheaf J AddCommGrpCat.{max u v}).map φ))

/- Lemma 18.3.1 (03CN) (3): categorical monomorphisms are exactly sectionwise injections. -/
@[stacks 03CN "sectionwise injectivity"]
#check (Sheaf.mono_iff_app_injective φ :
  Mono φ ↔ ∀ U : C, Function.Injective (φ.hom.app (op U)))

/- Lemma 18.3.1 (03CN) (3), local form: local injectivity is componentwise injectivity. -/
@[stacks 03CN "local injectivity"]
#check (Sheaf.isLocallyInjective_iff_injective φ :
  Sheaf.IsLocallyInjective φ ↔
    ∀ U : Cᵒᵖ, Function.Injective (φ.hom.app U))

/- Lemma 18.3.1 (03CN) (4): cokernels are obtained by sheafifying presheaf cokernels. -/
@[stacks 03CN "cokernels"]
#check (Sheaf.cokernelSheafificationIso φ :
  cokernel φ ≅
    (presheafToSheaf J AddCommGrpCat.{max u v}).obj
      (cokernel ((sheafToPresheaf J AddCommGrpCat.{max u v}).map φ)))

/- Lemma 18.3.1 (03CN) (5): categorical epimorphisms are exactly locally surjective maps. -/
@[stacks 03CN "local surjectivity"]
#check (Sheaf.isLocallySurjective_iff_epi'
    AddCommGrpCat.{max u v} φ :
  Sheaf.IsLocallySurjective φ ↔ Epi φ)

variable (S : ShortComplex (Sheaf J AddCommGrpCat.{max u v}))

/- Lemma 18.3.1 (03CN) (6): exactness is equivalent to the reusable local section-lifting
predicate. -/
@[stacks 03CN "local exactness"]
#check (ShortComplex.exact_iff_locally_surjective_sections S :
  S.Exact ↔ S.IsSectionwiseLocallyExact)

/- The categorical core of the preceding local lifting criterion. -/
#check (ShortComplex.exact_iff_isLocallySurjective_kernel_lift S :
  S.Exact ↔ Sheaf.IsLocallySurjective (kernel.lift S.g S.f S.zero))

end CategoryTheory
