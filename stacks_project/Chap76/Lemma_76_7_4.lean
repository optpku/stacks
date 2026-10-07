module

public import stacks_project.Chap76.Definition_76_7_2_Differentials
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- Lemma 76.7.4: let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic spaces
over `S`. Then `Ω[f]` is a quasi-coherent `𝒪_X`-module. -/
@[stacks 04CV]
instance isQuasicoherent_relativeDifferentials {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    (relativeDifferentials f).IsQuasicoherent :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
