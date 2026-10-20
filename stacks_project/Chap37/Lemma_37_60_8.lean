module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.PseudoCoherent.Finite
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 37.60.8: a finite morphism of schemes is pseudo-coherent if and only if
the pushforward of its structure sheaf is pseudo-coherent as a module. -/
@[stacks 0AVX]
#check (AlgebraicGeometry.PseudoCoherent.iff_pushforward_of_isFinite :
  ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) [AlgebraicGeometry.IsFinite f],
    AlgebraicGeometry.PseudoCoherent f ↔
      SheafOfModules.IsPseudoCoherent
        ((AlgebraicGeometry.Scheme.Modules.pushforward f).obj
          (SheafOfModules.unit X.ringCatSheaf : X.Modules)))
