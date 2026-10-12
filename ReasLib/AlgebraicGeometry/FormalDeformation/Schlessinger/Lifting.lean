/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.SmallExtensionComparison
public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation
public import ReasLib.AlgebraicGeometry.FormalDeformation.Schlessinger

/-!
# Lifting along a small extension after pushforward

In a predeformation category satisfying (S2), a morphism into the pushforward
of a cospan-square object along its explicit kernel-difference map yields a
lift through the second leg of the square.
-/

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]

namespace CategoryTheory.Functor

/-- A small-extension pushforward square admits the required lift under (S2). -/
theorem exists_hom_of_pushforward (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [IsPredeformationCategory p] [HasSchlessingerS2 p]
    {A A1 A2 : ArtinianLocalAlgCat Λ k}
    (f1 : A1 ⟶ A) (f2 : A2 ⟶ A) [IsSmallExtension f2]
    (h : A1 ⟶ A2) (hh : h ≫ f2 = f1) {y x1 x2 x : F}
    (c : y ⟶ x2) (d : y ⟶ x1) (a2 : x2 ⟶ x) (a1 : x1 ⟶ x)
    (h_sq : CommSq c d a2 a1)
    (hc : p.IsHomLift (cospanPullbackSnd f1 f2 h hh) c)
    (hd : p.IsHomLift (cospanPullbackFst f1 f2 h hh) d)
    (ha2 : p.IsHomLift f2 a2) (ha1 : p.IsHomLift f1 a1)
    {gy : F} (φ : y ⟶ gy)
    (hφ : p.IsHomLift (cospanPullbackDiff h hh) φ) :
    Nonempty (x1 ⟶ gy) → ∃ b : x1 ⟶ x2, b ≫ a2 = a1 := sorry

end CategoryTheory.Functor
