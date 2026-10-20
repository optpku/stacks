module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.Representability
import StacksCheckRecall

/-!
# Lemma 108.5.2

The structure morphism of the Grothendieck Quot functor over `B` is separated,
and locally of finite presentation when the source module is of finite
presentation.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 108.5.2 (1): the structure morphism of `quot f F` over `B` is
separated. -/
@[stacks 0DM3] #check (AlgebraicGeometry.AlgebraicSpace.Quot.instIsSeparatedOver :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B) [FinitePresentation f]
    [Separated f] (F : X.Modules) [F.IsQuasicoherent],
    AlgebraicGeometry.AlgebraicSpace.Quot.IsSeparatedOver
      (AlgebraicGeometry.AlgebraicSpace.Quot.quot f F))

/- Lemma 108.5.2 (2): if `F` is of finite presentation, then the structure
morphism of `quot f F` over `B` is locally of finite presentation. -/
@[stacks 0DM3] #check
  (AlgebraicGeometry.AlgebraicSpace.Quot.quot_isLocallyOfFinitePresentationOver :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B) [FinitePresentation f]
      [Separated f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFinitePresentation],
      IsLocallyOfFinitePresentationOver (AlgebraicGeometry.AlgebraicSpace.Quot.quot f F))
