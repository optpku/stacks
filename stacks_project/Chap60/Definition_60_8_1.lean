module

public import stacks_project.Chap60.«60_8_1_1»
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

variable (S : Scheme.{u}) (I : S.IdealSheafData)
variable (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
variable (h_compatible :
  ∀ (V : S.affineOpens) (f : Γ(S, V)),
    (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
      (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
variable (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)

/- Definition 60.8.1: in Situation 60.7.5, `RelativeCRIS` is the repository
   representation of the category `CRIS(X/S, I, γ)` of divided-power thickenings. -/
@[stacks 07I6] #check (RelativeCRIS S I γ h_compatible X x₀)
