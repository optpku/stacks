module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.ZMod.Basic
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.TypeConditions
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.Full

/-!
# The p-adic formal spectrum

The formal spectrum of the p-adic integers is the fppf sheafification of the
colimit of the affine schemes `Spec (ZMod (p ^ (n + 1)))`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

/-- The base scheme `Spec ℤ` of the p-adic thickening system. -/
abbrev padicBase := Spec (CommRingCat.of ℤ)

/-- The full chosen big fppf site over `Spec ℤ`. -/
abbrev padicSite : GrothendieckTopology (Over padicBase) :=
  ChosenBigFppfSite.full.bigTopology padicBase

/-- The affine scheme `Spec (ZMod (p ^ (n + 1)))` as an object over `Spec ℤ`. -/
def padicOver (p : ℕ) [Fact p.Prime] (n : ℕ) : Over padicBase :=
  Over.mk (Spec.map (CommRingCat.ofHom (Int.castRingHom (ZMod (p ^ (n + 1))))))

/-- The canonical quotient induces a successor thickening
`Spec (ZMod (p ^ (n + 1))) ⟶ Spec (ZMod (p ^ (n + 2)))` over `Spec ℤ`. -/
def padicSucc (p : ℕ) [Fact p.Prime] (n : ℕ) : padicOver p n ⟶ padicOver p (n + 1) :=
  Over.homMk
    (Spec.map (CommRingCat.ofHom (ZMod.castHom (pow_dvd_pow p (Nat.le_succ (n + 1))) _)))
    sorry

/-- The sequential diagram of affine p-adic thickenings `Spec (ZMod (p ^ (n + 1)))`. -/
def padicThickenings (p : ℕ) [Fact p.Prime] : ℕ ⥤ Over padicBase :=
  Functor.ofSequence (padicSucc p)

/-- The stage indexed by `n` of the p-adic thickening diagram is `padicOver p n`. -/
theorem padicThickenings_obj (p : ℕ) [Fact p.Prime] (n : ℕ) :
    (padicThickenings p).obj n = padicOver p n := rfl

/-- Each stage `Spec (ZMod (p ^ (n + 1)))` of the p-adic thickening diagram is affine. -/
instance padicThickenings_obj_isAffine (p : ℕ) [Fact p.Prime] (n : ℕ) :
    IsAffine ((padicThickenings p).obj n).left := by
  change IsAffine (Spec (CommRingCat.of (ZMod (p ^ (n + 1)))))
  infer_instance

/-- Every transition map of the p-adic thickening diagram is a thickening. -/
instance padicThickenings_map_isThickening (p : ℕ) [Fact p.Prime] {n m : ℕ} (f : n ⟶ m) :
    IsThickening ((padicThickenings p).map f).left := sorry

/-- The Yoneda colimit of the p-adic thickenings, before fppf sheafification. -/
def padicSpectrumPresheaf (p : ℕ) [Fact p.Prime] : (Over padicBase)ᵒᵖ ⥤ Type :=
  colimit (padicThickenings p ⋙ yoneda)

/-- The p-adic formal spectrum as the fppf sheafification of the universe-raised
Yoneda colimit of its affine thickenings. -/
def padicSpectrum (p : ℕ) [Fact p.Prime] : Sheaf padicSite (Type 1) :=
  (presheafToSheaf padicSite (Type 1)).obj
    (padicSpectrumPresheaf p ⋙ uliftFunctor.{1, 0})

/-- The underlying presheaf of the p-adic formal spectrum is the sheafification
of the universe-raised Yoneda colimit of its affine thickenings. -/
theorem padicSpectrum_eq (p : ℕ) [Fact p.Prime] :
    (padicSpectrum p).obj =
      sheafify padicSite (padicSpectrumPresheaf p ⋙ uliftFunctor.{1, 0}) := rfl

/-- The presheaf underlying the p-adic formal spectrum satisfies fppf descent. -/
theorem padicSpectrum_isSheaf (p : ℕ) [Fact p.Prime] :
    Presheaf.IsSheaf padicSite (padicSpectrum p).obj :=
  (padicSpectrum p).property

/-- The p-adic formal spectrum is a Noetherian affine formal algebraic space
on the full chosen big fppf site, including its fixed-site presentation condition. -/
instance padic_isNoetherianAffine (p : ℕ) [Fact p.Prime] :
    AlgebraicGeometry.IsNoetherianAffine (𝒮 := ChosenBigFppfSite.full)
      (padicSpectrum p) := sorry

end AlgebraicGeometry.AffineFormalAlgebraicSpace
