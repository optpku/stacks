module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree
public import stacks_project.Chap109.Lemma_109_11_1_Substack
public import stacks_project.Chap109.Lemma_109_9_1_Substack
public import stacks_project.Chap109.Lemma_109_9_3_HigherDirectImage

/-!
# The geometrically reduced connected locus of curves is contained in the h0,1 locus

As open substacks of 𝒞urves, 𝒞urves^{grc, 1} is contained in 𝒞urves^{h0, 1}.
In particular, a family of curves whose geometric fibres are reduced, connected,
and of dimension 1 has R^1 f_* 𝒪_X finite locally free, with formation commuting
with arbitrary base change.

-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.ObjectProperty CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/-- Lemma 109.11.2 (1): we have 𝒞urves^{grc, 1} ⊂ 𝒞urves^{h0, 1} as open
substacks of 𝒞urves. -/
@[stacks 0E6L]
theorem geometricallyReducedConnectedDim1_le_h0Dim1 (S : Scheme.{u}) :
    geometricallyReducedConnectedDim1 S ≤ h0Dim1 S :=
  sorry

/-- Lemma 109.11.2 (2): if a family of curves has classifying morphism factoring
through 𝒞urves^{grc, 1}, then R^1 f_* 𝒪_X is a finite locally free 𝒪_S-module. -/
@[stacks 0E6L]
theorem higherDirectImageOne_isFiniteLocallyFree_of_geometricallyReducedConnectedDim1
    {S : Scheme.{u}} (P : Obj S) (h : geometricallyReducedConnectedDim1 S P) :
    SheafOfModules.IsFiniteLocallyFree (higherDirectImageOne (hom P)) :=
  sorry

/-- Lemma 109.11.2 (3): if a family of curves has classifying morphism factoring
through 𝒞urves^{grc, 1}, then formation of R^1 f_* 𝒪_X commutes with arbitrary
base change through the canonical comparison. -/
@[stacks 0E6L]
theorem higherDirectImageOne_commutesWithBaseChange_of_geometricallyReducedConnectedDim1
    {S : Scheme.{u}} (P : Obj S) (h : geometricallyReducedConnectedDim1 S P)
    {Z : AlgebraicSpace S} (g : Z ⟶ ofOver (base P)) :
    IsIso (higherDirectImageOneBaseChangeHom (hom P) g) :=
  sorry

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
