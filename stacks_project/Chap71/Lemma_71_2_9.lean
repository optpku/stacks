module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Sections
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap69.Lemma_69_20_4_Pullback
public import stacks_project.Chap71.Lemma_71_2_3_WeaklyAssociated

/-!
# Lemma 71.2.9

Restriction of global sections of a quasi-coherent module along an étale morphism
of algebraic spaces is injective when the weakly associated locus is contained in
the image of the map on points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Lemma 71.2.9: for a scheme `S`, an algebraic space `X` over `S`, and a
quasi-coherent `𝒪_X`-module `F`, if `f : U ⟶ X` is étale and
`F.weakAss ⊆ Set.range (Points.map f)`, then the restriction map
`sectionsPullback f F : F.sections → ((pullback f).obj F).sections`
is injective. -/
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
