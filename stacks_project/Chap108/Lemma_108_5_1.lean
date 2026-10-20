module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.Diagonal
import StacksCheckRecall

/-!
# Lemma 108.5.1

The relative diagonal of the Grothendieck Quot functor over `B` is a closed
immersion, and of finite presentation when the source module is of finite type.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 108.5.1 (1): the diagonal of `quot f F` over `B` is a closed immersion. -/
@[stacks 0DM2] #check (AlgebraicGeometry.AlgebraicSpace.Quot.isClosedImmersion_diagonal :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B) [FinitePresentation f]
    [Separated f] (F : X.Modules) [F.IsQuasicoherent],
    SchemeOver.IsClosedImmersion (Limits.diag (AlgebraicGeometry.AlgebraicSpace.Quot.quot f F)))

/- Lemma 108.5.1 (2): if `F` is of finite type, the diagonal of `quot f F`
over `B` is of finite presentation. -/
@[stacks 0DM2] #check (AlgebraicGeometry.AlgebraicSpace.Quot.finitePresentation_diagonal :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B) [FinitePresentation f]
    [Separated f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType],
    SchemeOver.IsFinitePresentation
      (Limits.diag (AlgebraicGeometry.AlgebraicSpace.Quot.quot f F)))
