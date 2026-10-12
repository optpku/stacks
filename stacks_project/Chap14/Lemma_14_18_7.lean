/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.DoldKan.Reflects
import StacksCheckRecall

/-!
@stack 017W

# Lemma 14.18.7 compatibility facade

Mathlib's reflection typeclasses are the categorical owner. ReasLib adds only the lower-face
componentwise bridge used by this source statement; no proof-local faithful or reflection
instances are required.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicTopology
open scoped Simplicial

universe u v

namespace CategoryTheory.Abelian.DoldKan.N.lowerFace

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {U V : SimplicialObject A} (f : U ⟶ V)

/- Lemma 14.18.7 (1): normalization reflects degreewise monomorphisms. -/
@[stacks 017W "Lemma 14.18.7 (1)"]
#check (app.mono_of_normalized (f := f) :
  (∀ i : ℕ, Mono (((Abelian.DoldKan.N.lowerFace (A := A)).map f).f i)) →
    ∀ i : ℕ, Mono (f.app (op ⦋i⦌)))

/- Lemma 14.18.7 (2): normalization reflects degreewise epimorphisms. -/
@[stacks 017W "Lemma 14.18.7 (2)"]
#check (app.epi_of_normalized (f := f) :
  (∀ i : ℕ, Epi (((Abelian.DoldKan.N.lowerFace (A := A)).map f).f i)) →
    ∀ i : ℕ, Epi (f.app (op ⦋i⦌)))

/- Lemma 14.18.7 (3): normalization reflects degreewise isomorphisms. -/
@[stacks 017W "Lemma 14.18.7 (3)"]
#check (app.isIso_of_normalized (f := f) :
  (∀ i : ℕ, IsIso (((Abelian.DoldKan.N.lowerFace (A := A)).map f).f i)) →
    ∀ i : ℕ, IsIso (f.app (op ⦋i⦌)))

end CategoryTheory.Abelian.DoldKan.N.lowerFace
