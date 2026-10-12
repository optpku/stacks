/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.LocallySurjective
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

/- Lemma 65.5.9: let `S` be a scheme and let `F`, `G` be sheaves of sets
`(Over S)ᵒᵖ ⥤ Type u` on `(Sch/S)_fppf`. If `a : F ⟶ G` is a representable
transformation that is flat, locally of finite presentation, and surjective
in the sense of
`(over (@Flat ⊓ @LocallyOfFinitePresentation ⊓ @Surjective)).presheaf`,
then `a` is surjective as a map of sheaves in the sense of Sites
Definition 7.11.1, i.e. `Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) a`. -/
@[stacks 05VM] #check (AlgebraicGeometry.Scheme.isLocallySurjective_of_representable_fppf :
    ∀ {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u} (a : F ⟶ G),
      Presheaf.IsSheaf (Scheme.fppfTopology.over S) F →
      Presheaf.IsSheaf (Scheme.fppfTopology.over S) G →
      (over (@Flat ⊓ @LocallyOfFinitePresentation ⊓ @Surjective :
        MorphismProperty Scheme.{u})).presheaf a →
      Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) a)
