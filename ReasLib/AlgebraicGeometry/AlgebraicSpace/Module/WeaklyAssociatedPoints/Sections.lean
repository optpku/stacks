module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.WeaklyAssociatedPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback.Sections
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Sections

/-! # Global sections and weakly associated points of algebraic-space modules -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Pullback of global sections of a quasi-coherent module along an étale morphism
is injective when its image contains the weakly associated locus. -/
@[stacks 0CUP]
theorem injective_sectionsPullback_of_weakAss_subset
    {S : Scheme.{u}} {X U : AlgebraicSpace S} (f : U ⟶ X) [Etale f]
    (F : X.Modules) [F.IsQuasicoherent]
    (h : F.weakAss ⊆ Set.range (Points.map f)) :
    Function.Injective (sectionsPullback f F) :=
  sorry

/-- A global section of a quasi-coherent module is zero if it pulls back to zero
along an étale morphism whose image contains the weakly associated locus. -/
theorem sectionsPullback_eq_zero_of_weakAss_subset
    {S : Scheme.{u}} {X U : AlgebraicSpace S} (f : U ⟶ X) [Etale f]
    (F : X.Modules) [F.IsQuasicoherent]
    (h : F.weakAss ⊆ Set.range (Points.map f)) (s : F.sections)
    (hs : sectionsPullback f F s = 0) : s = 0 :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
