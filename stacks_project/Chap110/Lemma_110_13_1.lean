module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening
public import stacks_project.Chap94.Definition_94_12_1_Representable
public import stacks_project.Chap96.Definition_96_11_1_QCoh

/-!
# Quasi-coherent modules on a formal algebraic space need not form an abelian category
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.GroupoidsOver
open FiberedCategoryOver

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.QCoh

/-- The base scheme `Spec ℤ` of the p-adic thickening system. -/
abbrev padicBase := Spec (CommRingCat.of ℤ)

/-- The big fppf site `(Sch / Spec ℤ)_fppf`. -/
abbrev padicSite : GrothendieckTopology (Over padicBase) :=
  Scheme.fppfTopology.over padicBase

/-- The affine scheme `Spec (ZMod (p ^ (n + 1)))` as an object of `(Sch / Spec ℤ)`. -/
def padicOver (p : ℕ) [Fact p.Prime] (n : ℕ) : Over padicBase :=
  Over.mk (Spec.map (CommRingCat.ofHom (Int.castRingHom (ZMod (p ^ (n + 1))))))

/-- The successor thickening `Spec (ZMod (p ^ (n + 1))) ⟶ Spec (ZMod (p ^ (n + 2)))`
as a morphism over `Spec ℤ`. -/
def padicSucc (p : ℕ) [Fact p.Prime] (n : ℕ) : padicOver p n ⟶ padicOver p (n + 1) :=
  Over.homMk
    (Spec.map (CommRingCat.ofHom (ZMod.castHom (pow_dvd_pow p (Nat.le_succ (n + 1))) _)))
    sorry

/-- The `ℕ`-indexed diagram of affine p-adic thickenings `Spec (ZMod (p ^ (n + 1)))`. -/
def padicThickenings (p : ℕ) [Fact p.Prime] : ℕ ⥤ Over padicBase :=
  Functor.ofSequence (padicSucc p)

/-- Objects of `padicThickenings p` are the affine schemes `padicOver p n`. -/
theorem padicThickenings_obj (p : ℕ) [Fact p.Prime] (n : ℕ) :
    (padicThickenings p).obj n = padicOver p n := sorry

/-- Each stage `Spec (ZMod (p ^ (n + 1)))` of the p-adic thickening diagram is affine. -/
instance padicThickenings_obj_isAffine (p : ℕ) [Fact p.Prime] (n : ℕ) :
    IsAffine ((padicThickenings p).obj n).left := sorry

/-- Transition maps of `padicThickenings p` are thickenings. -/
instance padicThickenings_map_isThickening (p : ℕ) [Fact p.Prime] {n m : ℕ} (f : n ⟶ m) :
    IsThickening ((padicThickenings p).map f).left := sorry

/-- The yoneda-colimit presheaf of `padicThickenings p`, before fppf sheafification. -/
def padicSpectrumPresheaf (p : ℕ) [Fact p.Prime] : (Over padicBase)ᵒᵖ ⥤ Type :=
  colimit (padicThickenings p ⋙ yoneda)

/-- The fppf sheaf colimit of `padicThickenings p` on `(Sch / Spec ℤ)_fppf`. -/
def padicSpectrum (p : ℕ) [Fact p.Prime] : Sheaf padicSite (Type 1) :=
  (presheafToSheaf padicSite (Type 1)).obj
    (padicSpectrumPresheaf p ⋙ uliftFunctor.{1, 0})

/-- The underlying presheaf of `padicSpectrum p` is the sheafification of the
universe-raised yoneda colimit of `padicThickenings p`. -/
theorem padicSpectrum_eq (p : ℕ) [Fact p.Prime] :
    (padicSpectrum p).obj =
      sheafify padicSite (padicSpectrumPresheaf p ⋙ uliftFunctor.{1, 0}) := sorry

/-- `padicSpectrum p` is an fppf sheaf by sheafification of the universe-raised
yoneda colimit of `padicThickenings p`. -/
theorem padicSpectrum_isSheaf (p : ℕ) [Fact p.Prime] :
    Presheaf.IsSheaf padicSite (padicSpectrum p).obj := sorry

/-- The category fibred in groupoids associated to a set-valued presheaf on `(Sch / S)`
with values in `Type (u + 1)`, obtained by the discrete Grothendieck construction and
forgetting from sets to groupoids. The value universe is the sheafification universe
`u + 1`, so the construction lands in `GroupoidsOver S`. -/
abbrev ofPresheafGroupoids {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type (u + 1)) :
    GroupoidsOver S :=
  (Sets.toGroupoids (Over S)).obj ((Sets.ofPresheaf (Over S)).obj F)

/-- `ofPresheafGroupoids F` is the groupoid fibration of the discrete Grothendieck
construction of `F`. -/
theorem ofPresheafGroupoids_spec {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type (u + 1)) :
    ofPresheafGroupoids F =
      (Sets.toGroupoids (Over S)).obj ((Sets.ofPresheaf (Over S)).obj F) := sorry

/-- The p-adic spectrum is the fppf sheaf colimit of the affine thickening diagram
`padicThickenings p`, and the adic limit ring `ℤ_[p]` is Noetherian. -/
theorem padic_isNoetherianAffine (p : ℕ) [Fact p.Prime] :
    padicSpectrum p =
        (presheafToSheaf padicSite (Type 1)).obj
          (colimit (padicThickenings p ⋙ yoneda) ⋙ uliftFunctor.{1, 0}) ∧
      IsNoetherianRing ℤ_[p] := sorry

/-- Lemma 110.13.1: the category of quasi-coherent modules on a formal algebraic space
is not abelian in general, even if the space is a Noetherian affine formal algebraic
space. The source witness is the stack in setoids of the fppf sheaf colimit of
`padicThickenings p`. -/
@[stacks 0ALG]
theorem not_abelian (p : ℕ) [Fact p.Prime] :
    ¬ Nonempty (Abelian (QCoh (ofPresheafGroupoids (padicSpectrum p).obj))) := sorry

end AlgebraicGeometry.GroupoidsOver.QCoh
