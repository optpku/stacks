module

public import stacks_project.Chap100.Definition_100_9_1_Immersion
import StacksCheckRecall

@[expose] public section

/- Definition 100.9.1 (1): a morphism of algebraic stacks is called an open
immersion if it is representable, and an open immersion in the sense of
Section 100.3. -/
@[stacks 04YL] #check AlgebraicGeometry.Groupoids.Hom.OpenImmersion

/- Definition 100.9.1 (2): a morphism of algebraic stacks is called a closed
immersion if it is representable, and a closed immersion in the sense of
Section 100.3. -/
@[stacks 04YL] #check AlgebraicGeometry.Groupoids.Hom.ClosedImmersion

/- Definition 100.9.1 (3): a morphism of algebraic stacks is called an
immersion if it is representable, and an immersion in the sense of
Section 100.3. -/
@[stacks 04YL] #check AlgebraicGeometry.Groupoids.Hom.Immersion
