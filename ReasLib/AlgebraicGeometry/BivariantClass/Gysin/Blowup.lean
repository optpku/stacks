module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.ExcessConormal
public import ReasLib.AlgebraicGeometry.BivariantClass.Gysin.BaseChange
public import ReasLib.AlgebraicGeometry.BivariantClass.Gysin.Flat

/-!
# Gysin formula for blowups

Restriction of a blowup Gysin class is the top Chern class of the dual excess
conormal kernel composed with flat pullback along the exceptional projection.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.IsBlowup

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass

open Scheme.Hom.VirtualNormalBundle

/-- For a blowup with regular closed center over a universally catenary dimension-function
base, existence of a Gysin map gives a regular-immersion–smooth factorization with a
normal-bundle deformation realization. On every rank locus of the dual excess conormal
kernel and in every integer degree, restriction of the blowup Gysin coefficient equals
the top Chern component composed with exceptional flat pullback. -/
theorem blowup_restrict_gysin_eq_topChern_flatPullback
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X X' : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType X'.hom]
    (I : X.left.IdealSheafData) [IsRegularImmersion I.subschemeι]
    (b : X' ⟶ X) [IsBlowup b.left I] (hb : HasGysinMap b) :
    ∃ (P : Over S) (finiteTypeP : LocallyOfFiniteType P.hom)
      (i : X' ⟶ P) (h : P ⟶ X) (regularI : IsRegularImmersion i.left)
      (smoothH : Smooth h.left) (hfac : i ≫ h = b),
    ∃ (e : Scheme.Modules.dual (Scheme.Hom.normalSheaf i.left) ≅
        Scheme.Hom.conormalSheaf i.left)
      (D : ClosedDeformation X'.hom (i.left.coborderRange.ι ≫ P.hom)
        i.left.liftCoborder
        (by rw [← Category.assoc, i.left.liftCoborder_ι]; exact Over.w i)
        (Gysin.normalBundle i.left e).toCoborder),
    ∀ (r : ℕ) (p : ℤ),
      let π := exceptionalProjectionOverBase I b
      let Fdual := AlgebraicGeometry.IsBlowup.excessConormalDual I b.left
      let U := (Scheme.Modules.rankClopen Fdual r).toOpens
      let πU := ComponentRestriction.hom π U ⊤ (by simp)
      ComponentRestriction.restrict δ π p U ⊤ (by simp)
          (restrict δ (exceptionalι I b) π (centerι I)
            (exceptionalSquare_isPullback I b) p
            (Gysin.factorizationClassDegree δ b i h hfac e D p)) =
        let topChern := ChernClass.rankComponent δ
          ((I.comap b.left).subschemeι ≫ X'.hom)
          (Scheme.Modules.dual (AlgebraicGeometry.IsBlowup.excessConormal I b.left))
          r (Fin.last r)
        let flatCoefficient := flatPullbackDegree δ π (p - r)
        let c := comp δ (𝟙 (ComponentRestriction.over (exceptionalOver I b) U)) πU
          topChern
          (ComponentRestriction.restrict δ π (p - r) U ⊤ (by simp) flatCoefficient)
        (by
          have c := c
          rw [Category.id_comp] at c
          have degree : (r : ℤ) + (p - r) = p := by omega
          exact degree ▸ c) := sorry

end AlgebraicGeometry.BivariantClass
