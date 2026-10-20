module

public import ReasLib.AlgebraicGeometry.Scheme.Spec.AlmostBlowup
public import ReasLib.AlgebraicGeometry.Scheme.AlmostBlowup.Square
public import ReasLib.AlgebraicGeometry.Scheme.Frobenius.Colimit.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Characteristic
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.CatCommSqOver

/-!
# Frobenius-colimit comparison for a principal-center almost blowup

This module constructs the canonical restriction square on finite locally free modules over
Frobenius-colimit structure sheaves for an affine principal-center almost blowup square.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Spec.PrincipalCenter

/-- The canonical almost blowup square determined by a quotient and a principal center. -/
def almostBlowupSquare (A : CommRingCat.{u}) (f : A) (J : Ideal A)
    (hJfg : J.FG) (hJ : ∃ n : ℕ, ∀ x ∈ J, f ^ n * x = 0) : Square Scheme.{u} :=
  (quotientMap_isAlmostBlowupSquare A f J hJfg hJ).square

namespace FrobeniusColimit

/-- The base vertex of the canonical principal-center almost blowup square has the
characteristic of the coefficient ring. -/
instance almostBlowupSquareX4IsCharP (p : ℕ) (A : CommRingCat.{u})
    [CharP A p] (f : A) (J : Ideal A) (hJfg : J.FG)
    (hJ : ∃ n : ℕ, ∀ x ∈ J, f ^ n * x = 0) :
    Scheme.IsCharP (almostBlowupSquare A f J hJfg hJ).X₄ p := sorry

/-- The quotient vertex of the canonical principal-center almost blowup square inherits the
characteristic of the base. -/
instance almostBlowupSquareX2IsCharP (p : ℕ) (A : CommRingCat.{u})
    [CharP A p] (f : A) (J : Ideal A) (hJfg : J.FG)
    (hJ : ∃ n : ℕ, ∀ x ∈ J, f ^ n * x = 0) :
    Scheme.IsCharP (almostBlowupSquare A f J hJfg hJ).X₂ p := sorry

/-- The principal-center vertex of the canonical almost blowup square inherits the
characteristic of the base. -/
instance almostBlowupSquareX3IsCharP (p : ℕ) (A : CommRingCat.{u})
    [CharP A p] (f : A) (J : Ideal A) (hJfg : J.FG)
    (hJ : ∃ n : ℕ, ∀ x ∈ J, f ^ n * x = 0) :
    Scheme.IsCharP (almostBlowupSquare A f J hJfg hJ).X₃ p := sorry

/-- The exceptional vertex of the canonical principal-center almost blowup square inherits the
characteristic of the quotient vertex. -/
instance almostBlowupSquareX1IsCharP (p : ℕ) (A : CommRingCat.{u})
    [CharP A p] (f : A) (J : Ideal A) (hJfg : J.FG)
    (hJ : ∃ n : ℕ, ∀ x ∈ J, f ^ n * x = 0) :
    Scheme.IsCharP (almostBlowupSquare A f J hJfg hJ).X₁ p := sorry

open AlgebraicGeometry.Scheme.FrobeniusColimit

/-- The canonical restriction square on finite locally free modules over Frobenius-colimit
structure sheaves for a principal-center almost blowup square. -/
def restrictionSquare (p : ℕ) [Fact p.Prime]
    (A : CommRingCat.{u}) [CharP A p] (f : A) (J : Ideal A)
    (hJfg : J.FG) (hJ : ∃ n : ℕ, ∀ x ∈ J, f ^ n * x = 0) :
    let sq := almostBlowupSquare A f J hJfg hJ
    CategoricalPullback.CatCommSqOver
      (ModuleModel.pullback p sq.f₁₃) (ModuleModel.pullback p sq.f₁₂)
      (finiteLocallyFreeModules p sq.X₄) :=
  let sq := almostBlowupSquare A f J hJfg hJ
  { fst := ModuleModel.pullback p sq.f₃₄
    snd := ModuleModel.pullback p sq.f₂₄
    iso := (ModuleModel.pullbackCompIso p sq.f₁₃ sq.f₃₄).symm ≪≫
      eqToIso (congrArg (fun h : sq.X₁ ⟶ sq.X₄ ↦ ModuleModel.pullback p h) sq.fac.symm) ≪≫
      ModuleModel.pullbackCompIso p sq.f₁₂ sq.f₂₄ }

/-- The first projection of the canonical restriction square is pullback from the base to the
principal center. -/
theorem restrictionSquare_fst (p : ℕ) [Fact p.Prime]
    (A : CommRingCat.{u}) [CharP A p] (f : A) (J : Ideal A)
    (hJfg : J.FG) (hJ : ∃ n : ℕ, ∀ x ∈ J, f ^ n * x = 0) :
    (restrictionSquare p A f J hJfg hJ).fst =
      ModuleModel.pullback p (almostBlowupSquare A f J hJfg hJ).f₃₄ := sorry

/-- The second projection of the canonical restriction square is pullback from the base to the
quotient vertex. -/
theorem restrictionSquare_snd (p : ℕ) [Fact p.Prime]
    (A : CommRingCat.{u}) [CharP A p] (f : A) (J : Ideal A)
    (hJfg : J.FG) (hJ : ∃ n : ℕ, ∀ x ∈ J, f ^ n * x = 0) :
    (restrictionSquare p A f J hJfg hJ).snd =
      ModuleModel.pullback p (almostBlowupSquare A f J hJfg hJ).f₂₄ := sorry

/-- The structural isomorphism of the canonical restriction square is induced by the square
equation and functoriality of pullback. -/
theorem restrictionSquare_iso (p : ℕ) [Fact p.Prime]
    (A : CommRingCat.{u}) [CharP A p] (f : A) (J : Ideal A)
    (hJfg : J.FG) (hJ : ∃ n : ℕ, ∀ x ∈ J, f ^ n * x = 0) :
    let sq := almostBlowupSquare A f J hJfg hJ
    (restrictionSquare p A f J hJfg hJ).iso =
      (ModuleModel.pullbackCompIso p sq.f₁₃ sq.f₃₄).symm ≪≫
        eqToIso
          (congrArg (fun h : sq.X₁ ⟶ sq.X₄ ↦ ModuleModel.pullback p h) sq.fac.symm) ≪≫
        ModuleModel.pullbackCompIso p sq.f₁₂ sq.f₂₄ := sorry

/-- The canonical comparison from the Frobenius-colimit module model on the base to the
categorical pullback of the models on the principal-center and quotient vertices over the
exceptional vertex. -/
def comparison (p : ℕ) [Fact p.Prime]
    (A : CommRingCat.{u}) [CharP A p] (f : A) (J : Ideal A)
    (hJfg : J.FG) (hJ : ∃ n : ℕ, ∀ x ∈ J, f ^ n * x = 0) :=
  (restrictionSquare p A f J hJfg hJ).comparison

/-- The canonical restriction comparison for a principal-center almost blowup square is an
equivalence when the quotient ideal is finitely generated and annihilated by a power of the
principal generator. -/
instance comparisonIsEquivalence (p : ℕ) [Fact p.Prime]
    (A : CommRingCat.{u}) [CharP A p] (f : A) (J : Ideal A)
    (hJfg : J.FG) (hJ : ∃ n : ℕ, ∀ x ∈ J, f ^ n * x = 0) :
    (comparison p A f J hJfg hJ).IsEquivalence := sorry

end FrobeniusColimit

end AlgebraicGeometry.Spec.PrincipalCenter
