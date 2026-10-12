/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap60.Definition_60_8_4
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Zariski.Big
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Crystalline

/-- The site functor sending a crystalline object over `X` to its source over `S` by
postcomposition with `x₀ ≫ I.subschemeι`. -/
noncomputable def bigStructureFunctor {p : ℕ} [Fact (Nat.Prime p)]
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U))) :
    RelativeCRIS S I γ h_compatible X x₀ ⥤ Over S :=
  crystallineForgetful S I γ h_compatible s X x₀ h_p ⋙
    Scheme.Zariski.Big.map (x₀ ≫ I.subschemeι)

/-- The structure functor is objectwise the source object `U` over `X` postcomposed to `S`. -/
theorem bigStructureFunctor_obj {p : ℕ} [Fact (Nat.Prime p)]
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
    (c : RelativeCRIS S I γ h_compatible X x₀) :
    (bigStructureFunctor S I γ h_compatible s X x₀ h_p).obj c =
      Over.mk (c.1.source.hom ≫ x₀ ≫ I.subschemeι) := sorry

/-- The structure functor factors through `Over X` and the intermediate closed subscheme. -/
theorem bigStructureFunctor_factorization {p : ℕ} [Fact (Nat.Prime p)]
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U))) :
    bigStructureFunctor S I γ h_compatible s X x₀ h_p =
      crystallineForgetful S I γ h_compatible s X x₀ h_p ⋙
        Scheme.Zariski.Big.map x₀ ⋙
          Scheme.Zariski.Big.map I.subschemeι := sorry

/-- The site functor defining the big crystalline structure morphism is cocontinuous. -/
instance bigStructureFunctor_isCocontinuous {p : ℕ} [Fact (Nat.Prime p)]
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U))) :
    (bigStructureFunctor S I γ h_compatible s X x₀ h_p).IsCocontinuous
      (crystallineZariskiTopology S I γ h_compatible X x₀)
      S.bigZariskiTopology := sorry

end AlgebraicGeometry.Scheme.Crystalline

end
