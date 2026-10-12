/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Sheaves.PUnit
public import ReasLib.CategoryTheory.Functor.Algebraic.Basic
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe w v u

section

variable {C : Type u} [Category.{v} C] (F : C ⥤ Type w) [IsAlgebraicStructure C F]

/- The limit and colimit clauses are represented by mathlib's canonical comparison isomorphisms,
rather than by projection formulas or a parallel package. The local mono and epi statements are
the two source clauses not already exposed by a single canonical declaration for the pair `(C, F)`.
This keeps the exact `IsAlgebraicStructure C F` specialization while making the comparison maps
available for later sheaf and stalk arguments. -/

/- Lemma 6.15.3 (1): the underlying type of the final object is canonically equivalent to the
singleton type. -/
@[stacks 007O "underlying type of the final object"]
#check ((((PreservesTerminal.iso F) ≪≫ Types.terminalIso).toEquiv) :
  F.obj (⊤_ C) ≃ PUnit)

variable {ι : Type w} (A : ι → C) [HasProduct A] [PreservesLimit (Discrete.functor A) F]

/- Lemma 6.15.3 (2): the underlying type of a product is canonically the product of the
underlying types. -/
@[stacks 007O "underlying type of a product"]
#check (PreservesProduct.iso F A : F.obj (∏ᶜ A) ≅ ∏ᶜ fun i ↦ F.obj (A i))

variable {A₁ B C₁ : C} (f : A₁ ⟶ B) (g : C₁ ⟶ B) [HasPullback f g]
  [PreservesLimit (cospan f g) F]

/- Lemma 6.15.3 (3): the underlying type of a fibre product is canonically the fibre product of
the underlying maps. -/
@[stacks 007O "underlying type of a fibre product"]
#check (PreservesPullback.iso F f g :
  F.obj (pullback f g) ≅ pullback (F.map f) (F.map g))

variable {A₂ B₂ : C} (a b : A₂ ⟶ B₂) [HasEqualizer a b]
  [PreservesLimit (parallelPair a b) F]

/- Lemma 6.15.3 (4): the underlying map from an equalizer exhibits the equalizer of the two
underlying maps. -/
@[stacks 007O "underlying type and map of an equalizer"]
#check (PreservesEqualizer.iso F a b :
  F.obj (equalizer a b) ≅ equalizer (F.map a) (F.map b))

/- Lemma 6.15.3 (5): a morphism is a monomorphism if and only if its underlying map is
injective. -/
@[stacks 007O "monomorphisms are exactly underlying injections"]
#check mono_iff_underlying_injective F

/- Lemma 6.15.3 (6): a morphism whose underlying map is surjective is an epimorphism. -/
@[stacks 007O "underlying surjections are epimorphisms"]
#check epi_of_underlying_surjective F

variable {I : Type v} [Category.{v} I] [IsFiltered I] (D : I ⥤ C) [HasColimit D]
  [PreservesColimit D F]

/- Lemma 6.15.3 (7): the underlying type of any filtered colimit is canonically the filtered
colimit of the underlying types. -/
@[stacks 007O "underlying type of a filtered colimit"]
#check (preservesColimitIso F D : F.obj (colimit D) ≅ colimit (D ⋙ F))

end
