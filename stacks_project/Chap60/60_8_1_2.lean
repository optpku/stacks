module

public import stacks_project.Chap60.«60_8_1_2_CrystallineObject»
public import stacks_project.Chap60.«60_8_1_1»
public import ReasLib.RingTheory.Localization.AtPrime.Int
import Mathlib.Tactic.CrossRefAttribute

open AlgebraicGeometry CategoryTheory

@[expose] public section

universe u

/-- A morphism of trivial crystalline objects is induced by the same morphism on the source and
its underlying scheme map on the identity thickenings. -/
def trivialCrystallineObjectHom {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme) {U V : Over X} (φ : U ⟶ V) :
    CrystallineObject.Hom
      (trivialCrystallineObject I γ h_compatible X x₀ U)
      (trivialCrystallineObject I γ h_compatible X x₀ V) where
  source := φ
  thickening := φ.left
  source_comm := sorry
  base_comm := sorry
  ideal_compatible := sorry
  dividedPowers_compatible := sorry

/-- 60.8.1.2: In Situation 60.7.5, the one-sided-inverse functor
`Sch/X ⥤ RelativeCRIS(X/S)` sends `U` to the identity thickening `(U, U, ∅)`. -/
@[stacks 07I8]
noncomputable def crystallineTrivialFunctor (p : ℕ) [Fact (Nat.Prime p)]
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U))) :
    Over X ⥤ RelativeCRIS S I γ h_compatible X x₀ where
  obj := fun U ↦
    ⟨trivialCrystallineObject I γ h_compatible X x₀ U, sorry⟩
  map := fun {U V} φ ↦ trivialCrystallineObjectHom I γ h_compatible X x₀ φ
  map_id := sorry
  map_comp := sorry

/-- The trivial functor is a one-sided inverse of the forgetful functor, expressed
as a natural isomorphism rather than a definitional equality of functors. -/
@[stacks 07I8]
theorem crystallineTrivialFunctor_oneSidedInverse (p : ℕ) [Fact (Nat.Prime p)]
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U))) :
    Nonempty ((crystallineTrivialFunctor p S I γ h_compatible s X x₀ h_p) ⋙
      crystallineForgetful S I γ h_compatible s X x₀ h_p ≅ 𝟭 (Over X)) := sorry

/-- The trivial functor is left adjoint to the specified crystalline forgetful
functor. -/
@[stacks 07I8]
theorem crystallineTrivialFunctor_leftAdjoint (p : ℕ) [Fact (Nat.Prime p)]
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U))) :
    Nonempty (crystallineTrivialFunctor p S I γ h_compatible s X x₀ h_p ⊣
      crystallineForgetful S I γ h_compatible s X x₀ h_p) := sorry

/-- The object map of the crystalline trivial functor is the explicit identity thickening. -/
@[stacks 07I8]
lemma crystallineTrivialFunctor_obj (p : ℕ) [Fact (Nat.Prime p)]
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U))) (U : Over X) :
    (crystallineTrivialFunctor p S I γ h_compatible s X x₀ h_p).obj U =
      (⟨trivialCrystallineObject I γ h_compatible X x₀ U, sorry⟩ :
        RelativeCRIS S I γ h_compatible X x₀) := sorry

/-- The morphism map of the crystalline trivial functor is induced by the underlying map of an
arrow in `Over X`. -/
@[stacks 07I8]
lemma crystallineTrivialFunctor_map (p : ℕ) [Fact (Nat.Prime p)]
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
    {U V : Over X} (φ : U ⟶ V) :
    (crystallineTrivialFunctor p S I γ h_compatible s X x₀ h_p).map φ =
      trivialCrystallineObjectHom I γ h_compatible X x₀ φ := sorry

/-- Every object in the image of the crystalline trivial functor is compatible with the fixed
divided-power structure on the base. -/
@[stacks 07I8]
lemma crystallineTrivialFunctor_isCrystalline (p : ℕ) [Fact (Nat.Prime p)]
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U))) (U : Over X) :
    CrystallineBaseCompatible I γ h_compatible x₀
      ((crystallineTrivialFunctor p S I γ h_compatible s X x₀ h_p).obj U).1 := sorry

end
