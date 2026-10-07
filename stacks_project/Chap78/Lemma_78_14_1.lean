module

public import stacks_project.Chap78.Lemma_78_14_1_Crystal
public import stacks_project.Chap78.Lemma_78_14_1_CardinalGeneration
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 78.14.1: if every morphism of a set-theoretic pre-relation diagram of schemes is
flat, there exists a cardinal `κ` such that every object of `CQC(X)` is the directed
colimit of its `κ`-generated submodules. -/
@[stacks 077Z] #check
  (AlgebraicGeometry.Scheme.RelDiagram.Crystal.exists_cardinal_kappaGeneratedSubobjects_isDirectedColimit :
    ∀ (X : AlgebraicGeometry.Scheme.RelDiagram.{u}) [∀ φ, Flat (X.map φ)],
      ∃ κ : Cardinal.{u}, ∀ F : AlgebraicGeometry.Scheme.RelDiagram.Crystal X,
        DirectedOn (· ≤ ·)
            (AlgebraicGeometry.Scheme.RelDiagram.Crystal.kappaGeneratedSubobjects κ F) ∧
          IsLUB (AlgebraicGeometry.Scheme.RelDiagram.Crystal.kappaGeneratedSubobjects κ F)
            (fun i ↦ (⊤ : Subobject (F.obj i))))
