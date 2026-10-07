module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat.Epi
import StacksCheckRecall

universe u

open AlgebraicGeometry CategoryTheory

/- Lemma 35.35.1: a surjective and flat morphism is an epimorphism in the category of
schemes. -/
@[stacks 02VW] #check
  (AlgebraicGeometry.Flat.epi_of_surjective :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [Surjective f], Epi f)
