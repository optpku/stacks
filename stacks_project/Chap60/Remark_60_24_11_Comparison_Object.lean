module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Pullbacks
public import ReasLib.RingTheory.DividedPowers.Extension.Criteria
public import stacks_project.Chap60.«60_8_1_1»
public import stacks_project.Chap60.«60_9_1_1_Site»
public import stacks_project.Chap60.Proposition_60_21_1

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Crystalline
open CrystallineObject

universe u

namespace AlgebraicGeometry.Scheme.Crystalline

variable {p : ℕ} [Fact (Nat.Prime p)]
variable {A : Type u} [CommRing A] {IA : Ideal A} (γA : DividedPowers IA)
variable {Y : Scheme.{u}} (yToS : Y ⟶ Spec.{u} (.of A))
variable (I : (Spec.{u} (.of A)).IdealSheafData)
variable (γS : ∀ V : (Spec.{u} (.of A)).affineOpens, DividedPowers (I.ideal V))
variable (h_compatible :
  ∀ (V : (Spec.{u} (.of A)).affineOpens) (f : Γ(Spec.{u} (.of A), V)),
    (γS V).IsDPMorphism (γS ((Spec.{u} (.of A)).affineBasicOpen f))
      ((Spec.{u} (.of A)).presheaf.map
        (homOfLE ((Spec.{u} (.of A)).basicOpen_le f)).op).hom)
variable (hI : specIdealEqOfIdealTop IA I)
variable (hγ : specDividedPowersEq IA γA I γS)

/-- Closed fibre `X = Y ×_S S₀` of a smooth lift `Y → Spec A` along `S₀ = V(I)`. -/
def smoothLift : Scheme.{u} :=
  pullback yToS I.subschemeι

/-- Closed immersion of the closed fibre into the smooth lift. -/
def smoothLift_inclusion : smoothLift yToS I ⟶ Y :=
  pullback.fst yToS I.subschemeι

/-- Structure map of the closed fibre over `S₀ = V(I)`. -/
def smoothLift_x₀ : smoothLift yToS I ⟶ I.subscheme :=
  pullback.snd yToS I.subschemeι

/-- Unfolding of the closed fibre as a scheme-theoretic fibre product. -/
theorem smoothLift_eq :
    smoothLift yToS I = pullback yToS I.subschemeι :=
  sorry

/-- The closed-fibre inclusion is the first projection of the fibre product. -/
theorem smoothLift_inclusion_eq :
    smoothLift_inclusion yToS I = pullback.fst yToS I.subschemeι :=
  sorry

/-- The closed-fibre structure map is the second projection of the fibre product. -/
theorem smoothLift_x₀_eq :
    smoothLift_x₀ yToS I = pullback.snd yToS I.subschemeι :=
  sorry

/-- Affine-section ring map `A → Γ(T, V)` induced by a morphism to `Spec A`. -/
def affineSectionMap {T : Scheme.{u}} (g : T ⟶ Spec.{u} (.of A))
    (V : T.affineOpens) : A →+* Γ(T, V) :=
  (g.appLE ⊤ V.1 le_top).hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom

/-- Unfolding of the affine-section map as `g.appLE` after `ΓSpecIso`. -/
theorem affineSectionMap_eq {T : Scheme.{u}} (g : T ⟶ Spec.{u} (.of A))
    (V : T.affineOpens) :
    affineSectionMap g V =
      (g.appLE ⊤ V.1 le_top).hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom :=
  sorry

/-- Unique divided-power extension of `γA` along a ring map, when an extension exists. -/
def extensionAlong {B : Type u} [CommRing B] (f : A →+* B)
    (h : γA.extendsAlong f) : γA.Extension f :=
  Classical.choice
    ((DividedPowers.extendsAlong_iff_nonempty_extension γA f).mp h)

/-- The chosen extension is a divided-power morphism along `f`. -/
theorem extensionAlong_spec {B : Type u} [CommRing B] (f : A →+* B)
    (h : γA.extendsAlong f) :
    DividedPowers.IsDPMorphism γA (extensionAlong γA f h).dividedPowers f :=
  sorry

/-- Transport divided powers along an equality of ideals. -/
def dividedPowers_ofIdealEq {R : Type u} [CommSemiring R] {J K : Ideal R}
    (h : J = K) (γ : DividedPowers J) : DividedPowers K :=
  h ▸ γ

/-- Affine-section maps of a smooth morphism `Y → Spec A` are flat. -/
theorem affineSectionMap_flat [Smooth yToS] (V : Y.affineOpens) :
    (affineSectionMap yToS V).Flat :=
  sorry

/-- Affine-section maps of a smooth lift extend the divided powers `γA`. -/
theorem affineSectionMap_extendsAlong [Smooth yToS] (V : Y.affineOpens) :
    γA.extendsAlong (affineSectionMap yToS V) :=
  sorry

/-- Image of `IA` along the affine-section map recovers the ideal of `X` in `Y`. -/
theorem affineSectionMap_map_eq_ker_ideal [Smooth yToS]
    (hI : specIdealEqOfIdealTop IA I) (V : Y.affineOpens) :
    IA.map (affineSectionMap yToS V) =
      (smoothLift_inclusion yToS I).ker.ideal V :=
  sorry

/-- Divided powers on the ideal of `X` in `Y`, obtained by uniquely extending `γA`. -/
def smoothLiftDividedPowers [Smooth yToS] (V : Y.affineOpens) :
    DividedPowers ((smoothLift_inclusion yToS I).ker.ideal V) :=
  dividedPowers_ofIdealEq
    (affineSectionMap_map_eq_ker_ideal yToS I hI V)
    (extensionAlong γA (affineSectionMap yToS V)
      (DividedPowers.extendsAlong_of_flat γA (affineSectionMap yToS V)
        (affineSectionMap_flat yToS V))).dividedPowers

/-- The affine-section divided powers of the smooth lift make `A → Γ(Y, V)` a
divided-power morphism, and they are the unique such extension of `γA`. -/
theorem smoothLiftDividedPowers_spec [Smooth yToS] (V : Y.affineOpens) :
    DividedPowers.IsDPMorphism γA (smoothLiftDividedPowers γA yToS I hI V)
      (affineSectionMap yToS V) :=
  sorry

/-- Uniqueness of the affine-section divided-power extension of `γA`. -/
theorem smoothLiftDividedPowers_unique [Smooth yToS] (V : Y.affineOpens)
    (δ : γA.Extension (affineSectionMap yToS V)) :
    δ.dividedPowers =
      dividedPowers_ofIdealEq
        (Eq.symm (affineSectionMap_map_eq_ker_ideal yToS I hI V))
        (smoothLiftDividedPowers γA yToS I hI V) :=
  sorry

/-- Compatibility of the extended divided powers on basic opens of `Y`. -/
theorem smoothLiftDividedPowers_compatible [Smooth yToS]
    (V : Y.affineOpens) (f : Γ(Y, V)) :
    (smoothLiftDividedPowers γA yToS I hI V).IsDPMorphism
      (smoothLiftDividedPowers γA yToS I hI (Y.affineBasicOpen f))
      (Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op).hom :=
  sorry

/-- Nilpotence of `p` on `A` implies local nilpotence of `p` on the closed fibre. -/
theorem smoothLift_p_nilpotent (hpnil : IsNilpotent (p : A)) [Smooth yToS] :
    ∀ U : (smoothLift yToS I).affineOpens,
      IsNilpotent (p : Γ(smoothLift yToS I, U)) :=
  sorry

/-- Affine-section map of an open of the smooth lift. -/
def affineSectionMap_over (U : Y.Opens) (V : U.toScheme.affineOpens) :
    A →+* Γ(U.toScheme, V) :=
  affineSectionMap (U.ι ≫ yToS) V

/-- Affine-section maps of an open of a smooth lift are flat. -/
theorem affineSectionMap_over_flat [Smooth yToS] (U : Y.Opens)
    (V : U.toScheme.affineOpens) :
    (affineSectionMap_over yToS U V).Flat :=
  sorry

/-- Image of `IA` along an open of the smooth lift recovers the restricted
closed-fibre ideal. -/
theorem affineSectionMap_over_map_eq_ker_ideal [Smooth yToS]
    (hI : specIdealEqOfIdealTop IA I) (U : Y.Opens)
    (V : U.toScheme.affineOpens) :
    IA.map (affineSectionMap_over yToS U V) =
      (pullback.snd (smoothLift_inclusion yToS I) U.ι).ker.ideal V :=
  sorry

/-- Divided powers on an open of the smooth lift, uniquely extended from `γA`. -/
def smoothLiftDividedPowers_over [Smooth yToS] (U : Y.Opens)
    (V : U.toScheme.affineOpens) :
    DividedPowers ((pullback.snd (smoothLift_inclusion yToS I) U.ι).ker.ideal V) :=
  dividedPowers_ofIdealEq
    (affineSectionMap_over_map_eq_ker_ideal yToS I hI U V)
    (extensionAlong γA (affineSectionMap_over yToS U V)
      (DividedPowers.extendsAlong_of_flat γA (affineSectionMap_over yToS U V)
        (affineSectionMap_over_flat yToS U V))).dividedPowers

/-- Compatibility of restricted divided powers on basic opens. -/
theorem smoothLiftDividedPowers_over_compatible [Smooth yToS] (U : Y.Opens)
    (V : U.toScheme.affineOpens) (f : Γ(U.toScheme, V)) :
    (smoothLiftDividedPowers_over γA yToS I hI U V).IsDPMorphism
      (smoothLiftDividedPowers_over γA yToS I hI U (U.toScheme.affineBasicOpen f))
      (U.toScheme.presheaf.map (homOfLE (U.toScheme.basicOpen_le f)).op).hom :=
  sorry

/-- Source of the crystalline object obtained by restricting the smooth lift to an
open of `Y`. -/
def smoothLiftSource_over (U : Y.Opens) :
    Over (smoothLift yToS I) :=
  Over.mk (pullback.fst (smoothLift_inclusion yToS I) U.ι)

end AlgebraicGeometry.Scheme.Crystalline
