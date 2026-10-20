module

public import stacks_project.Chap60.Situation_60_7_5
public import stacks_project.Chap60.«60_10_0_2_ModuleSheaf»
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.Affine
public import ReasLib.RingTheory.Localization.AtPrime.Int
import Mathlib.Tactic.CrossRefAttribute

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

@[expose] public section

universe u

/- Lemma 60.18.1 (07JJ): in Situation 60.7.5, a locally quasi-coherent
crystalline module has no positive-degree cohomology over a crystalline object
whose thickening or source is affine. -/
/-- Lemma 60.18.1: in Situation 60.7.5, a locally quasi-coherent crystalline
module has vanishing `H' q` over every crystalline object whose thickening or
source is affine, for every `q > 0`. -/
@[stacks 07JJ]
theorem crystallineModule_higherCohomology_isZero_of_affine
    (p : ℕ) [Fact (Nat.Prime p)]
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (X : Scheme.{u}) (f : X ⟶ I.subscheme)
    (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
    (F : CrystallineModuleSheaf S I γ h_compatible X f)
    [∀ A : CRIS S I γ h_compatible X f, (F.obj A).IsQuasicoherent]
    (A : CRIS S I γ h_compatible X f)
    (h_affine : IsAffine A.thickening ∨ IsAffine A.source.left)
    (q : ℕ) (hq : 0 < q) :
    IsZero
      (((SheafOfModules.toSheaf A.thickening.ringCatSheaf).obj (F.obj A)).H'
        q (⊤ : A.thickening.Opens)) := sorry
