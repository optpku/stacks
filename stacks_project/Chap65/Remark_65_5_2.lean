/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Sheaf
public import ReasLib.AlgebraicGeometry.Scheme.RepresentableProperty
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty Opposite

universe u

section

variable {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u} (a : F ⟶ G)
variable {Fₛ Gₛ : Sheaf (Scheme.fppfTopology.over S) (Type u)} (φ : Fₛ ⟶ Gₛ)

/- Remark 65.5.2: for `P = Surjective`, the phrase “let `F ⟶ G` be a surjective map”
is ambiguous among (i) Definition 65.5.1 representable-morphism surjectivity
`(over (@Surjective)).presheaf a`, (ii) Sites Definition 7.3.1 objectwise
presheaf surjectivity `∀ U, Function.Surjective (a.app (op U))`, and (iii) Sites
Definition 7.11.1 sheaf/local surjectivity `Sheaf.IsLocallySurjective φ`.
Unless otherwise stated, morphisms of algebraic spaces use (i). Lemma 65.5.9 is
a case where (i) implies (iii). -/
@[stacks 02YN] #check (AlgebraicGeometry.Scheme.representableMorphismProperty S
  (@Surjective : MorphismProperty Scheme.{u}) a : Prop)

/- Sites Definition 7.3.1: objectwise surjectivity of a map of Type-valued
presheaves. -/
#check (∀ U : Over S, Function.Surjective (a.app (op U)))

/- Sites Definition 7.11.1: surjectivity of a map of sheaves of sets. -/
#check (Sheaf.IsLocallySurjective φ)

/- Underlying-presheaf form of sheaf-local surjectivity used in Lemma 65.5.9. -/
#check Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) a

end
