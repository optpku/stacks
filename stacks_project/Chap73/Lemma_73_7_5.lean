module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import stacks_project.Chap65.Definition_65_12_5_ZariskiCover
public import stacks_project.Chap73.Definition_73_7_1_FppfCover
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Fppf.LocallySurjective
import StacksCheckRecall

/-!
# Surjectivity of the coproduct sheaf map of an fppf covering

An fppf covering family of algebraic spaces induces a locally surjective map
of fppf sheaves from the coproduct of the sources.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u v

/- Lemma 73.7.5: let `S` be a scheme and let `{f i : X_i i ⟶ X}` be an fppf
covering of algebraic spaces over `S`. Then the map of sheaves
`sheafCoproductDesc X_i f : ∐ (X_i i).functorOfPoints ⟶ X.functorOfPoints` is
surjective in the sense of Sites Definition 7.11.1, i.e.
`Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (sheafCoproductDesc X_i f)`.
See Remark 65.5.2 for the distinction from representable-morphism and objectwise
surjectivity. -/
@[stacks 0469]
#check (AlgebraicGeometry.AlgebraicSpace.FppfCovering.instIsLocallySurjective_sheafCoproductDesc :
    ∀ {S : Scheme.{u}} {ι : Type v}
    {X : AlgebraicSpace S} [Small.{u} ι] {X_i : ι → AlgebraicSpace S}
    {f : ∀ i, X_i i ⟶ X} [FppfCovering X_i f],
    Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (sheafCoproductDesc X_i f))
