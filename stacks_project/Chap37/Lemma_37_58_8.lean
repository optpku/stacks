module

public import ReasLib.AlgebraicGeometry.Scheme.Module.FinitePresentation.Relative.Exact
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

/- Lemma 37.58.8 (1): in a short exact sequence of quasi-coherent modules over a scheme,
relative finite presentation of the outer terms implies relative finite presentation of the
middle term. -/
@[stacks 09TD] #check
  (AlgebraicGeometry.Scheme.Modules.IsFinitePresentationOver.middle_of_shortExact :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
      {C : ShortComplex X.Modules} [C.X₁.IsQuasicoherent] [C.X₂.IsQuasicoherent]
      [C.X₃.IsQuasicoherent] (hC : C.ShortExact) (h₁ : C.X₁.IsFinitePresentationOver f)
      (h₃ : C.X₃.IsFinitePresentationOver f), C.X₂.IsFinitePresentationOver f)

/- Lemma 37.58.8 (2): in a short exact sequence of quasi-coherent modules over a scheme,
a finite-type left term and relatively finitely presented middle term imply relative finite
presentation of the right term. -/
@[stacks 09TD] #check
  (AlgebraicGeometry.Scheme.Modules.IsFinitePresentationOver.right_of_shortExact :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
      {C : ShortComplex X.Modules} [C.X₁.IsQuasicoherent] [C.X₂.IsQuasicoherent]
      [C.X₃.IsQuasicoherent] [C.X₁.IsFiniteType] (hC : C.ShortExact)
      (h₂ : C.X₂.IsFinitePresentationOver f), C.X₃.IsFinitePresentationOver f)
