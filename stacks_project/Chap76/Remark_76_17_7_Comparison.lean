module

public import stacks_project.Chap76.«76_17_4_1_Deformation»
public import stacks_project.Chap76.Lemma_76_17_4_Sheaf
public import stacks_project.Chap76.Lemma_76_17_5_Action
public import stacks_project.Chap76.Lemma_76_5_5_BaseChange
public import stacks_project.Chap76.Definition_76_7_2_Differentials

/-!
# Pullback thickenings as a special case of infinitesimal deformations of maps

When `B` is a thickening `Z ⊂ Z'` and `Y` is the fibre product `Z ×_{Z'} Y'`, the
conormal comparison `A : a^* C_{Y/Y'} ⟶ C_{X/X'}` is uniquely determined by `a`,
compatible local lifts are morphisms over `Z'` restricting to `a`, and the acting
Hom sheaf is taken relative to `Ω_{Y/Z}`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom.Deformation

variable {S : Scheme.{u}} {Z Z' X X' Y Y' : AlgebraicSpace S}

/-- The pulled comparison `g^* C_{Z/Z'} ⟶ a^* C_{Y/Y'}`, identifying
`g^* = (a ≫ h)^*` with `a^* h^*` via `Modules.pullbackComp`. -/
def pulledConormal (iZ : Z ⟶ Z') (iY : Y ⟶ Y') (h : Y ⟶ Z) (h' : Y' ⟶ Z')
    (a : X ⟶ Y) [IsThickening iZ] [IsFirstOrderThickening iY]
    (sqY : IsPullback h iY iZ h') :
    (Modules.pullback (a ≫ h)).obj (conormalSheaf iZ) ⟶
      (Modules.pullback a).obj (conormalSheaf iY) :=
  (Modules.pullbackComp a h).inv.app (conormalSheaf iZ) ≫
    (Modules.pullback a).map (Conormal.map sqY.toCommSq)

/-- `pulledConormal` is the `pullbackComp` inverse followed by the pullback of
`Conormal.map` of the cartesian square `Y = Z ×_{Z'} Y'`. -/
theorem pulledConormal_eq (iZ : Z ⟶ Z') (iY : Y ⟶ Y') (h : Y ⟶ Z) (h' : Y' ⟶ Z')
    (a : X ⟶ Y) [IsThickening iZ] [IsFirstOrderThickening iY]
    (sqY : IsPullback h iY iZ h') :
    pulledConormal iZ iY h h' a sqY =
      (Modules.pullbackComp a h).inv.app (conormalSheaf iZ) ≫
        (Modules.pullback a).map (Conormal.map sqY.toCommSq) :=
  sorry

/-- The pulled comparison `g^* C_{Z/Z'} ⟶ a^* C_{Y/Y'}` is an epimorphism. -/
instance pulledConormal_epi (iZ : Z ⟶ Z') (iY : Y ⟶ Y') (h : Y ⟶ Z) (h' : Y' ⟶ Z')
    (a : X ⟶ Y) [IsThickening iZ] [IsFirstOrderThickening iY]
    (sqY : IsPullback h iY iZ h') :
    Epi (pulledConormal iZ iY h h' a sqY) :=
  sorry

/-- A comparison `A : a^* C_{Y/Y'} ⟶ C_{X/X'}` is the unique map determined by `a`
when `pulledConormal ≫ A` recovers the canonical conormal map of `(g, g')`. -/
def IsDeterminedConormal (iZ : Z ⟶ Z') (iX : X ⟶ X') (iY : Y ⟶ Y')
    (h : Y ⟶ Z) (h' : Y' ⟶ Z') (g' : X' ⟶ Z') (a : X ⟶ Y)
    [IsThickening iZ] [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
    (sqY : IsPullback h iY iZ h') (sqX : CommSq (a ≫ h) iX iZ g')
    (A : (Modules.pullback a).obj (conormalSheaf iY) ⟶ conormalSheaf iX) : Prop :=
  pulledConormal iZ iY h h' a sqY ≫ A = Conormal.map sqX

/-- `IsDeterminedConormal` is the characterizing equation
`pulledConormal ≫ A = Conormal.map sqX`. -/
theorem isDeterminedConormal_iff (iZ : Z ⟶ Z') (iX : X ⟶ X') (iY : Y ⟶ Y')
    (h : Y ⟶ Z) (h' : Y' ⟶ Z') (g' : X' ⟶ Z') (a : X ⟶ Y)
    [IsThickening iZ] [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
    (sqY : IsPullback h iY iZ h') (sqX : CommSq (a ≫ h) iX iZ g')
    (A : (Modules.pullback a).obj (conormalSheaf iY) ⟶ conormalSheaf iX) :
    IsDeterminedConormal iZ iX iY h h' g' a sqY sqX A ↔
      pulledConormal iZ iY h h' a sqY ≫ A = Conormal.map sqX :=
  sorry

/-- In the pullback-over-thickening special case, a comparison
`A : a^* C_{Y/Y'} ⟶ C_{X/X'}` satisfying `IsDeterminedConormal` is unique. -/
theorem determinedConormal_unique (iZ : Z ⟶ Z') (iX : X ⟶ X') (iY : Y ⟶ Y')
    (h : Y ⟶ Z) (h' : Y' ⟶ Z') (g' : X' ⟶ Z') (a : X ⟶ Y)
    [IsThickening iZ] [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
    (sqY : IsPullback h iY iZ h') (sqX : CommSq (a ≫ h) iX iZ g')
    (A A' : (Modules.pullback a).obj (conormalSheaf iY) ⟶ conormalSheaf iX) :
    IsDeterminedConormal iZ iX iY h h' g' a sqY sqX A →
      IsDeterminedConormal iZ iX iY h h' g' a sqY sqX A' → A = A' :=
  sorry

/-- A local lift `a' : U' ⟶ Y'` over `Z'` whose restriction to
`U = X ×_{X'} U'` agrees with `a`. -/
def IsRestrictedLift (g' : X' ⟶ Z') (h' : Y' ⟶ Z') (iX : X ⟶ X') (iY : Y ⟶ Y')
    (a : X ⟶ Y) [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
    (U' : spacesEtaleSite X') (a' : U'.left ⟶ Y') : Prop :=
  a' ≫ h' = U'.hom ≫ g' ∧
    (toSource iX U' ≫ a) ≫ iY = closedι iX U' ≫ a'

/-- `IsRestrictedLift` is the over-`Z'` condition together with the restriction
equation `a'|_U = a|_U`. -/
theorem isRestrictedLift_iff (g' : X' ⟶ Z') (h' : Y' ⟶ Z') (iX : X ⟶ X')
    (iY : Y ⟶ Y') (a : X ⟶ Y)
    [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
    (U' : spacesEtaleSite X') (a' : U'.left ⟶ Y') :
    IsRestrictedLift g' h' iX iY a U' a' ↔
      a' ≫ h' = U'.hom ≫ g' ∧
        (toSource iX U' ≫ a) ≫ iY = closedι iX U' ≫ a' :=
  sorry

/-- The set of morphisms `U' ⟶ Y'` over `Z'` that restrict to `a` on `U`. -/
def restrictedSections (g' : X' ⟶ Z') (h' : Y' ⟶ Z') (iX : X ⟶ X') (iY : Y ⟶ Y')
    (a : X ⟶ Y) [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
    (U' : spacesEtaleSite X') : Set (U'.left ⟶ Y') :=
  {a' | IsRestrictedLift g' h' iX iY a U' a'}

/-- Membership in `restrictedSections` is the restriction-only lift predicate. -/
theorem mem_restrictedSections_iff (g' : X' ⟶ Z') (h' : Y' ⟶ Z') (iX : X ⟶ X')
    (iY : Y ⟶ Y') (a : X ⟶ Y)
    [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
    (U' : spacesEtaleSite X') (a' : U'.left ⟶ Y') :
    a' ∈ restrictedSections g' h' iX iY a U' ↔
      IsRestrictedLift g' h' iX iY a U' a' :=
  sorry

/-- For a determined conormal comparison `A`, the sheaf of Lemma 76.17.4 has
sections given by the restriction-only rule. -/
theorem sections_eq_restrictedSections (iZ : Z ⟶ Z') (iX : X ⟶ X') (iY : Y ⟶ Y')
    (h : Y ⟶ Z) (h' : Y' ⟶ Z') (g' : X' ⟶ Z') (a : X ⟶ Y)
    [IsThickening iZ] [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
    (sqY : IsPullback h iY iZ h') (sqX : CommSq (a ≫ h) iX iZ g')
    (A : (Modules.pullback a).obj (conormalSheaf iY) ⟶ conormalSheaf iX)
    (hA : IsDeterminedConormal iZ iX iY h h' g' a sqY sqX A)
    (U' : spacesEtaleSite X') :
    sections g' h' iX iY a A U' = restrictedSections g' h' iX iY a U' :=
  sorry

/-- The type of `𝒪_U`-linear maps `(a|_U)^* Ω_{Y/Z} ⟶ C_{U/U'}`. -/
abbrev closedParameterHom (iX : X ⟶ X') (h : Y ⟶ Z) (a : X ⟶ Y)
    [IsFirstOrderThickening iX] (U' : spacesEtaleSite X') :=
  (Modules.pullback (toSource iX U' ≫ a)).obj (relativeDifferentials h) ⟶
    conormalSheaf (closedι iX U')

/-- `closedParameterHom` is the Hom-type from the pulled relative differentials
`Ω_{Y/Z}` to the conormal sheaf of `U ⊂ U'`. -/
theorem closedParameterHom_eq (iX : X ⟶ X') (h : Y ⟶ Z) (a : X ⟶ Y)
    [IsFirstOrderThickening iX] (U' : spacesEtaleSite X') :
    closedParameterHom iX h a U' =
      ((Modules.pullback (toSource iX U' ≫ a)).obj (relativeDifferentials h) ⟶
        conormalSheaf (closedι iX U')) :=
  sorry

/-- The first-order factorization through `d_{Y/Z}` associated to a local
`Ω_{Y/Z}`-parameter. -/
def restrictedFactorization (iX : X ⟶ X') (iY : Y ⟶ Y') (h : Y ⟶ Z) (a : X ⟶ Y)
    [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
    (U' : spacesEtaleSite X') (θ : closedParameterHom iX h a U') :=
  factorizationMap h (closedι iX U') iY (toSource iX U' ≫ a)
    (ofCanonicalDerivation h
      ((Modules.pushforward (toSource iX U' ≫ a)).obj (conormalSheaf (closedι iX U')))
      (derivationOfPullback h (toSource iX U' ≫ a) θ))

/-- `restrictedFactorization` is `factorizationMap` of the `Z`-relative derivation
associated to `θ`. -/
theorem restrictedFactorization_eq (iX : X ⟶ X') (iY : Y ⟶ Y') (h : Y ⟶ Z)
    (a : X ⟶ Y) [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
    (U' : spacesEtaleSite X') (θ : closedParameterHom iX h a U') :
    restrictedFactorization iX iY h a U' θ =
      factorizationMap h (closedι iX U') iY (toSource iX U' ≫ a)
        (ofCanonicalDerivation h
          ((Modules.pushforward (toSource iX U' ≫ a)).obj
            (conormalSheaf (closedι iX U')))
          (derivationOfPullback h (toSource iX U' ≫ a) θ)) :=
  sorry

/-- A restricted lift `t` is the first-order perturbation of a restricted lift `s`
prescribed by a local Hom parameter from `a^* Ω_{Y/Z}`. -/
def IsRestrictedPerturbation (g' : X' ⟶ Z') (h' : Y' ⟶ Z') (iX : X ⟶ X')
    (iY : Y ⟶ Y') (h : Y ⟶ Z) (a : X ⟶ Y)
    [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
    (U' : spacesEtaleSite X') (θ : closedParameterHom iX h a U')
    (s t : U'.left ⟶ Y') : Prop :=
  IsRestrictedLift g' h' iX iY a U' s ∧
    IsRestrictedLift g' h' iX iY a U' t ∧
      ∃ sqS : CommSq (toSource iX U' ≫ a) (closedι iX U') iY s,
      ∃ sqT : CommSq (toSource iX U' ≫ a) (closedι iX U') iY t,
        Conormal.map sqS = Conormal.map sqT ∧
          structureMapDifference_restrict (closedι iX U') iY
              (toSource iX U' ≫ a) s t sqS.w.symm sqT.w.symm =
            restrictedFactorization iX iY h a U' θ

/-- `IsRestrictedPerturbation` is the pair of restricted lifts together with equal
conormal comparisons and the `Z`-relative derivation identity. -/
theorem isRestrictedPerturbation_iff (g' : X' ⟶ Z') (h' : Y' ⟶ Z') (iX : X ⟶ X')
    (iY : Y ⟶ Y') (h : Y ⟶ Z) (a : X ⟶ Y)
    [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
    (U' : spacesEtaleSite X') (θ : closedParameterHom iX h a U')
    (s t : U'.left ⟶ Y') :
    IsRestrictedPerturbation g' h' iX iY h a U' θ s t ↔
      IsRestrictedLift g' h' iX iY a U' s ∧
        IsRestrictedLift g' h' iX iY a U' t ∧
          ∃ sqS : CommSq (toSource iX U' ≫ a) (closedι iX U') iY s,
          ∃ sqT : CommSq (toSource iX U' ≫ a) (closedι iX U') iY t,
            Conormal.map sqS = Conormal.map sqT ∧
              structureMapDifference_restrict (closedι iX U') iY
                  (toSource iX U' ≫ a) s t sqS.w.symm sqT.w.symm =
                restrictedFactorization iX iY h a U' θ :=
  sorry

/-- The sheaf of Hom parameters from `a^* Ω_{Y/Z}` acts uniquely on restricted
lifts in the pullback-over-thickening diagram. -/
theorem existsUnique_restrictedPerturbation (iZ : Z ⟶ Z') (iX : X ⟶ X')
    (iY : Y ⟶ Y') (h : Y ⟶ Z) (h' : Y' ⟶ Z') (g' : X' ⟶ Z') (a : X ⟶ Y)
    [IsThickening iZ] [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
    (sqY : IsPullback h iY iZ h') (sqX : CommSq (a ≫ h) iX iZ g')
    (U' : spacesEtaleSite X') (θ : closedParameterHom iX h a U')
    (s : U'.left ⟶ Y') (hs : s ∈ restrictedSections g' h' iX iY a U') :
    ExistsUnique fun t : U'.left ⟶ Y' ↦
      IsRestrictedPerturbation g' h' iX iY h a U' θ s t :=
  sorry

/-- Given one restricted lift on `U'`, translation by Hom parameters from
`a^* Ω_{Y/Z}` is simply transitive in the pullback-over-thickening diagram. -/
theorem restricted_act_simplyTransitive (iZ : Z ⟶ Z') (iX : X ⟶ X')
    (iY : Y ⟶ Y') (h : Y ⟶ Z) (h' : Y' ⟶ Z') (g' : X' ⟶ Z') (a : X ⟶ Y)
    [IsThickening iZ] [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
    (sqY : IsPullback h iY iZ h') (sqX : CommSq (a ≫ h) iX iZ g')
    (U' : spacesEtaleSite X') (s t : U'.left ⟶ Y')
    (hs : s ∈ restrictedSections g' h' iX iY a U')
    (ht : t ∈ restrictedSections g' h' iX iY a U') :
    ExistsUnique fun θ : closedParameterHom iX h a U' ↦
      IsRestrictedPerturbation g' h' iX iY h a U' θ s t :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom.Deformation
