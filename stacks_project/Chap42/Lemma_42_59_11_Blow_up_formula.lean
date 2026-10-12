/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap42.Lemma_42_59_10
public import stacks_project.Chap42.Lemma_42_59_11_Blow_up_formula_Excess
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.FixedRank

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.IsBlowup
open Scheme.Hom.VirtualNormalBundle

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass

/-- Integer grading identity comparing the Gysin degree `c + (-t)` of a blowup with the
degree `r + (-r)` of `c_top ∘ π^*`. -/
theorem blowup_gysin_degree {c t r : ℕ}
    (hdeg : (c : ℤ) + (-(t : ℤ)) = (r : ℤ) + (-(r : ℤ))) :
    (r : ℤ) + (-(r : ℤ)) = (c : ℤ) + (-(t : ℤ)) := sorry

/-- The top Chern class of the dual excess conormal sheaf of a blowup, at globally
constant rank `r`. -/
noncomputable def excessTopChern
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X X' : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType X'.hom]
    (I : X.left.IdealSheafData) (b : X' ⟶ X) [IsBlowup b.left I]
    (r : ℕ) [Scheme.Modules.IsFiniteLocallyFreeOfRank r (excessConormalDual I b.left)] :
    BivariantClass δ (𝟙 (exceptionalOver I b)) (r : ℤ) :=
  ChernClass.FixedRank.component δ ((I.comap b.left).subschemeι ≫ X'.hom)
    (excessConormalDual I b.left) r (Fin.last r)

/-- `excessTopChern` is the canonical rank-`r` Chern component of the dual excess
conormal sheaf. -/
theorem excessTopChern_eq
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X X' : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType X'.hom]
    (I : X.left.IdealSheafData) (b : X' ⟶ X) [IsBlowup b.left I]
    (r : ℕ) [Scheme.Modules.IsFiniteLocallyFreeOfRank r (excessConormalDual I b.left)] :
    excessTopChern δ I b r =
      ChernClass.FixedRank.component δ ((I.comap b.left).subschemeι ≫ X'.hom)
        (excessConormalDual I b.left) r (Fin.last r) := sorry

/-- Lemma 42.59.11 (Blow up formula): in Situation 42.7.1, if `i : Z ⟶ X` is a regular
closed immersion of schemes locally of finite type over `S` and `b : X' ⟶ X` is the
blowup with center `Z`, and the Gysin map of `b` exists, then
`res(b^!) = c_top(F^∨) ∘ π^*` in `A^*(E ⟶ Z)`, where `F` is the kernel of the canonical
map `π^* C_{Z/X} ⟶ C_{E/X'}`. -/
@[stacks 0FVA]
theorem blowup_restrict_gysin_eq_topChern_flatPullback
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X X' : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType X'.hom]
    (I : X.left.IdealSheafData) [IsRegularImmersion I.subschemeι]
    (b : X' ⟶ X) [IsBlowup b.left I]
    [LocallyOfType RingHom.IsLocalCompleteIntersection b.left]
    (hb : HasGysinMap b)
    {P : Over S} [LocallyOfFiniteType P.hom]
    (ι : X' ⟶ P) (σ : P ⟶ X) (hι : IsImmersion ι.left)
    [IsClosedImmersion ι.left] [IsRegularImmersion ι.left]
    (hσ : Smooth σ.left) (hfac : ι ≫ σ = b)
    (t : ℕ) [Scheme.Hom.RelativeDimension σ.left t]
    (c : ℕ) [Scheme.Modules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf ι.left)]
    (e : Scheme.Modules.dual (Scheme.Hom.normalSheaf ι.left) ≅
      Scheme.Hom.conormalSheaf ι.left)
    (D : ClosedSpecialization δ X'.hom P.hom ι.left (Over.w ι)
      (ofNormalSheaf ι.left c e))
    (r : ℕ) [Scheme.Modules.IsFiniteLocallyFreeOfRank r (excessConormal I b.left)]
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r (excessConormalDual I b.left)]
    [Flat (exceptionalProjectionOverBase I b).left]
    [Scheme.Hom.RelativeDimension (exceptionalProjectionOverBase I b).left r]
    (hdeg : (c : ℤ) + (-(t : ℤ)) = (r : ℤ) + (-(r : ℤ))) :
    restrict δ (exceptionalι I b) (exceptionalProjectionOverBase I b) (centerι I)
        (exceptionalSquare_isPullback I b) ((c : ℤ) + (-(t : ℤ)))
        (canonicalGysinClass δ b ι σ hι hσ hfac (ofNormalSheaf ι.left c e) D c t) =
      Nonnegative.castGrading δ (blowup_gysin_degree hdeg)
        (idCompCast δ
          (comp δ (𝟙 (exceptionalOver I b)) (exceptionalProjectionOverBase I b)
            (excessTopChern δ I b r)
            (flatPullback δ (exceptionalProjectionOverBase I b) r))) := sorry

end AlgebraicGeometry.BivariantClass
