module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Deformation.Action

/-!
# Pullback thickenings as a special case of infinitesimal deformations of maps

When `B` is a thickening `Z ⊂ Z'` and `Y` is the fibre product `Z ×_{Z'} Y'`, the
conormal comparison `A : a^* C_{Y/Y'} ⟶ C_{X/X'}` is uniquely determined by `a`,
compatible local lifts are morphisms over `Z'` restricting to `a`, and the acting
Hom sheaf is taken relative to `Ω_{Y/Z}`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom.Deformation

variable {S : Scheme.{u}} {Z Z' X X' Y Y' : AlgebraicSpace S}

/-- The pulled comparison `g^* C_{Z/Z'} ⟶ a^* C_{Y/Y'}`, identifying
`g^* = (a ≫ h)^*` with `a^* h^*` via `Modules.pullbackCompIso`. -/
def pulledConormal (iZ : Z ⟶ Z') (iY : Y ⟶ Y') (h : Y ⟶ Z) (h' : Y' ⟶ Z')
    (a : X ⟶ Y) [IsThickening iZ] [IsFirstOrderThickening iY]
    (sqY : IsPullback h iY iZ h') :
    (Modules.pullback (a ≫ h)).obj (conormalSheaf iZ) ⟶
      (Modules.pullback a).obj (conormalSheaf iY) :=
  (Modules.pullbackCompIso a h).inv.app (conormalSheaf iZ) ≫
    (Modules.pullback a).map (Conormal.map sqY.toCommSq)

/-- `pulledConormal` is the `pullbackCompIso` inverse followed by the pullback of
`Conormal.map` of the cartesian square `Y = Z ×_{Z'} Y'`. -/
theorem pulledConormal_eq (iZ : Z ⟶ Z') (iY : Y ⟶ Y') (h : Y ⟶ Z) (h' : Y' ⟶ Z')
    (a : X ⟶ Y) [IsThickening iZ] [IsFirstOrderThickening iY]
    (sqY : IsPullback h iY iZ h') :
    pulledConormal iZ iY h h' a sqY =
      (Modules.pullbackCompIso a h).inv.app (conormalSheaf iZ) ≫
        (Modules.pullback a).map (Conormal.map sqY.toCommSq) :=
  rfl

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
  Iff.rfl

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
  Iff.rfl

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
  Iff.rfl

/-- For a determined conormal comparison, compatible sections are exactly the
local lifts over the thickened base restricting to the given map. -/
theorem sections_eq_restrictedSections (iZ : Z ⟶ Z') (iX : X ⟶ X') (iY : Y ⟶ Y')
    (h : Y ⟶ Z) (h' : Y' ⟶ Z') (g' : X' ⟶ Z') (a : X ⟶ Y)
    [IsThickening iZ] [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
    (sqY : IsPullback h iY iZ h') (sqX : CommSq (a ≫ h) iX iZ g')
    (A : (Modules.pullback a).obj (conormalSheaf iY) ⟶ conormalSheaf iX)
    (hA : IsDeterminedConormal iZ iX iY h h' g' a sqY sqX A)
    (U' : spacesEtaleSite X') :
    sections g' h' iX iY a A U' = restrictedSections g' h' iX iY a U' :=
  sorry

/-- Restricting a local lift over the thickened base preserves its base and
closed-fibre equations. -/
theorem mem_restrictedSections_restrictHom (g' : X' ⟶ Z') (h' : Y' ⟶ Z')
    (iX : X ⟶ X') (iY : Y ⟶ Y') (a : X ⟶ Y)
    [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
    {U' V' : spacesEtaleSite X'} (f : V' ⟶ U') (a' : U'.left ⟶ Y')
    (ha' : a' ∈ restrictedSections g' h' iX iY a U') :
    restrictHom f a' ∈ restrictedSections g' h' iX iY a V' :=
  sorry

/-- The presheaf of local lifts over the thickened base whose closed-fibre
restriction is the given map, with restriction by precomposition. -/
def restrictedSectionsPresheaf (g' : X' ⟶ Z') (h' : Y' ⟶ Z')
    (iX : X ⟶ X') (iY : Y ⟶ Y') (a : X ⟶ Y)
    [IsFirstOrderThickening iX] [IsFirstOrderThickening iY] :
    (spacesEtaleSite X')ᵒᵖ ⥤ Type (u + 1) where
  obj U' := { a' : U'.unop.left ⟶ Y' // a' ∈ restrictedSections g' h' iX iY a U'.unop }
  map f := TypeCat.ofHom fun a' ↦
    ⟨restrictHom f.unop a'.1,
      mem_restrictedSections_restrictHom g' h' iX iY a f.unop a'.1 a'.2⟩
  map_id U' := by
    apply ConcreteCategory.hom_ext
    intro a'
    apply Subtype.ext
    exact restrictHom_id U'.unop a'.1
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro a'
    apply Subtype.ext
    exact (restrictHom_comp g.unop f.unop a'.1).symm

/-- Local lifts over the thickened base with prescribed closed-fibre restriction
satisfy descent on the spaces-étale site. -/
theorem restrictedSectionsPresheaf_isSheaf (g' : X' ⟶ Z') (h' : Y' ⟶ Z')
    (iX : X ⟶ X') (iY : Y ⟶ Y') (a : X ⟶ Y)
    [IsFirstOrderThickening iX] [IsFirstOrderThickening iY] :
    Presheaf.IsSheaf (spacesEtaleTopology X')
      (restrictedSectionsPresheaf g' h' iX iY a) :=
  sorry

/-- The sheaf of local lifts over the thickened base with the prescribed
closed-fibre restriction. -/
def restrictedSectionsSheaf (g' : X' ⟶ Z') (h' : Y' ⟶ Z')
    (iX : X ⟶ X') (iY : Y ⟶ Y') (a : X ⟶ Y)
    [IsFirstOrderThickening iX] [IsFirstOrderThickening iY] :
    Sheaf (spacesEtaleTopology X') (Type (u + 1)) :=
  ⟨restrictedSectionsPresheaf g' h' iX iY a,
    restrictedSectionsPresheaf_isSheaf g' h' iX iY a⟩

/-- Evaluating the restricted-lift sheaf gives precisely the subtype of maps
satisfying the base and closed-fibre equations. -/
theorem restrictedSectionsSheaf_obj (g' : X' ⟶ Z') (h' : Y' ⟶ Z')
    (iX : X ⟶ X') (iY : Y ⟶ Y') (a : X ⟶ Y)
    [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
    (U' : spacesEtaleSite X') :
    (restrictedSectionsSheaf g' h' iX iY a).obj.obj (op U') =
      { a' : U'.left ⟶ Y' // a' ∈ restrictedSections g' h' iX iY a U' } :=
  rfl

/-- The first-order factorization through `d_{Y/Z}` associated to a local
`Ω_{Y/Z}`-parameter. -/
def restrictedFactorization (iX : X ⟶ X') (iY : Y ⟶ Y') (h : Y ⟶ Z) (a : X ⟶ Y)
    [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
    (U' : spacesEtaleSite X') (θ : parameterHom h iX (𝟙 Y) a U') :=
  factorizationMap (𝟙 Y ≫ h) (closedι iX U') iY (toSource iX U' ≫ a)
    (derivationOfPullback (𝟙 Y ≫ h) (toSource iX U' ≫ a) θ)

/-- The restricted factorization is the composite induced by the relative
 derivation associated to the local differential parameter. -/
theorem restrictedFactorization_eq (iX : X ⟶ X') (iY : Y ⟶ Y') (h : Y ⟶ Z)
    (a : X ⟶ Y) [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
    (U' : spacesEtaleSite X') (θ : parameterHom h iX (𝟙 Y) a U') :
    restrictedFactorization iX iY h a U' θ =
      factorizationMap (𝟙 Y ≫ h) (closedι iX U') iY (toSource iX U' ≫ a)
        (derivationOfPullback (𝟙 Y ≫ h) (toSource iX U' ≫ a) θ) :=
  rfl

/-- A restricted lift `t` is the first-order perturbation of a restricted lift `s`
prescribed by a local Hom parameter from `a^* Ω_{Y/Z}`. -/
def IsRestrictedPerturbation (g' : X' ⟶ Z') (h' : Y' ⟶ Z') (iX : X ⟶ X')
    (iY : Y ⟶ Y') (h : Y ⟶ Z) (a : X ⟶ Y)
    [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
    (U' : spacesEtaleSite X') (θ : parameterHom h iX (𝟙 Y) a U')
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
    (U' : spacesEtaleSite X') (θ : parameterHom h iX (𝟙 Y) a U')
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
  Iff.rfl

/-- The sheaf of Hom parameters from `a^* Ω_{Y/Z}` acts uniquely on restricted
lifts in the pullback-over-thickening diagram. -/
theorem existsUnique_restrictedPerturbation (iZ : Z ⟶ Z') (iX : X ⟶ X')
    (iY : Y ⟶ Y') (h : Y ⟶ Z) (h' : Y' ⟶ Z') (g' : X' ⟶ Z') (a : X ⟶ Y)
    [IsThickening iZ] [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
    (sqY : IsPullback h iY iZ h') (sqX : CommSq (a ≫ h) iX iZ g')
    (U' : spacesEtaleSite X') (θ : parameterHom h iX (𝟙 Y) a U')
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
    ExistsUnique fun θ : parameterHom h iX (𝟙 Y) a U' ↦
      IsRestrictedPerturbation g' h' iX iY h a U' θ s t :=
  sorry

/-- The zero differential parameter fixes every restricted lift. -/
theorem restricted_act_zero (iZ : Z ⟶ Z') (iX : X ⟶ X')
    (iY : Y ⟶ Y') (h : Y ⟶ Z) (h' : Y' ⟶ Z') (g' : X' ⟶ Z') (a : X ⟶ Y)
    [IsThickening iZ] [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
    (sqY : IsPullback h iY iZ h') (sqX : CommSq (a ≫ h) iX iZ g')
    (U' : spacesEtaleSite X') (s : U'.left ⟶ Y')
    (hs : s ∈ restrictedSections g' h' iX iY a U') :
    IsRestrictedPerturbation g' h' iX iY h a U' 0 s s :=
  sorry

/-- Perturbation by a sum of differential parameters is successive perturbation. -/
theorem restricted_act_add (iZ : Z ⟶ Z') (iX : X ⟶ X')
    (iY : Y ⟶ Y') (h : Y ⟶ Z) (h' : Y' ⟶ Z') (g' : X' ⟶ Z') (a : X ⟶ Y)
    [IsThickening iZ] [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
    (sqY : IsPullback h iY iZ h') (sqX : CommSq (a ≫ h) iX iZ g')
    (U' : spacesEtaleSite X') (θ η : parameterHom h iX (𝟙 Y) a U')
    (s t : U'.left ⟶ Y') :
    IsRestrictedPerturbation g' h' iX iY h a U' (θ + η) s t ↔
      ∃ r : U'.left ⟶ Y',
        IsRestrictedPerturbation g' h' iX iY h a U' η s r ∧
          IsRestrictedPerturbation g' h' iX iY h a U' θ r t :=
  sorry

/-- Restriction of local lifts is equivariant for restriction of differential
parameters relative to the closed base. -/
theorem restricted_act_naturality (iZ : Z ⟶ Z') (iX : X ⟶ X')
    (iY : Y ⟶ Y') (h : Y ⟶ Z) (h' : Y' ⟶ Z') (g' : X' ⟶ Z') (a : X ⟶ Y)
    [IsThickening iZ] [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
    (sqY : IsPullback h iY iZ h') (sqX : CommSq (a ≫ h) iX iZ g')
    {U' V' : spacesEtaleSite X'} (f : V' ⟶ U')
    (θ : parameterHom h iX (𝟙 Y) a U') (s t : U'.left ⟶ Y')
    (hst : IsRestrictedPerturbation g' h' iX iY h a U' θ s t) :
    IsRestrictedPerturbation g' h' iX iY h a V'
      (restrictParameter h iX (𝟙 Y) a f θ) (restrictHom f s) (restrictHom f t) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom.Deformation
