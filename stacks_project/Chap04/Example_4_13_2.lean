/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Types.Basic
import StacksCheckRecall

@[expose] public section


namespace CategoryTheory

universe u

variable {X Y : Type u} (f : X ⟶ Y)

/- The source asks for equivalences concerning morphisms in `Type`. The verified candidates are
the bundled-morphism theorems `mono_iff_injective` and `epi_iff_surjective` and their raw-function
variants `ofHom_mono_iff_injective` and `ofHom_epi_iff_surjective`. The bundled versions are the
better canonical surface because they preserve the categorical input instead of inserting
`ofHom`. This makes no generalization: specializing the two recalls to any `f : X ⟶ Y` recovers
the source clauses exactly, while leaving `Mono f` and `Epi f` directly reusable downstream. -/

/- Example 4.13.2 (1): in the category of sets, a morphism is a monomorphism
exactly when its underlying function is injective. This is the canonical theorem
`CategoryTheory.mono_iff_injective`. -/
@[stacks 003C "monomorphisms in Type are injective"]
#check (mono_iff_injective f : Mono f ↔ Function.Injective f)

/- Example 4.13.2 (2): in the category of sets, a morphism is an epimorphism
exactly when its underlying function is surjective. This is the canonical theorem
`CategoryTheory.epi_iff_surjective`. -/
@[stacks 003C "epimorphisms in Type are surjective"]
#check (epi_iff_surjective f : Epi f ↔ Function.Surjective f)

end CategoryTheory
